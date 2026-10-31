import CausalScaffold.Flat.Achronal

/-!
# `CausalScaffold.Flat.LipschitzGraph` — 1-Lipschitz (achronal) hypersurfaces of `𝐌ⁿ`: the null-line Cauchy criterion, causal convexity, the hub lemma, (CC′) transfer, domains of dependence

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257). No
b-label is certified: the passages are prose, and the module is the "general theory of 1-Lipschitz
surfaces embedded in Minkowski" the author asked for, of which Rem 2.2's hyperboloid is the
standard example. Design: `docs/BARBOT-WAVE3.md` §1 A–D (not §1E, the induced length). It extends
`CausalScaffold.Flat.Achronal` (`graph`, the achronal/acausal iffs, the `κ < 1` criterion
`isCauchySurface_graph`, the hyperboloid), which it does not duplicate. Line numbers are those of
the labelled file `papers/barbot/legacy/labeled/GHFspace.tex`.

* `[8.G]` (l.2307–2309, l.2320–2326; not certified):

  > $\widetilde{S}$ is the graph of a contracting map
  > $\varphi: {\mathbb R}^{n-1} \rightarrow {\mathbb R}$. […]
  > spacelike hypersurfaces
  > are achronal closed set, meaning that if $x$ and $y$
  > are two distinct points in $\widetilde{S}$, one cannot
  > be contained in the past of future cone of the other, i.e., we have
  > $\mid x-y \mid^{2}>0$.
* `bprop:danom`, l.2489–2491 (not certified; **false as written**, `docs/BARBOT-WAVE3.md` §0 W7):

  > Hence, for any $t$, every nonspacelike geodesic intersecting $\widetilde{S}$ meets
  > $\widetilde{S} \times \{ t \}$. It follows, thanks to proposition \ref{project}, that every
  > nonspacelike line of \mink meets ${\mathcal D}(\widetilde{S} \times \{ t \})$.

  Here `𝒟` is the developing map and `𝒟(S̃ × {t})` a developed slice, not the domain of
  dependence below. By the null-line criterion `isCauchySurface_graph_iff`, for a strictly
  contracting entire graph the claim of l.2491 says exactly that the developed slice is a Cauchy
  surface of all of `𝐌ⁿ`. The hyperboloid (Rem 2.2) is a strictly contracting entire graph whose
  domain of dependence is only the future cone (`dependenceDomain_hyperboloid`) and which is no
  Cauchy surface of `𝐌ⁿ`: the claim fails for it, which is W7's counterexample, and why the
  design repairs `bprop:danom` without slices.
* `Rem 2.2` (l.540–545; not certified):

  > in \mink, let $\Omega$ be a connected component of the negative cone $\{ Q< 0 \}$.
  > Then, $S = \Omega \cap \{ Q=-1 \}$ is a Cauchy hypersurface for $\Omega$. […]
  > The point is that $S$ is not a Cauchy hypersurface in \mink, therefore,
  > the inclusion $\Omega \subset {\bf M}^{n}$ is not a Cauchy embedding.

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; the library's `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions: Barbot's `n` is `d + 1`.

## What is proved

* **A.** `timeSub f = t − f(x)` (`graph f = T⁻¹(0)`, `mem_graph_iff_timeSub`),
  `IsStrictContraction f` (`|f x − f y| < ‖x − y‖`, `x ≠ y`) ↔ `graph f` acausal
  (`isAcausal_graph_iff_isStrictContraction`); `isTimeFunction_timeSub` (DEC-10), `T` monotone
  along `≤` for 1-Lipschitz `f` and **strictly** increasing for strictly contracting `f`
  (`timeSub_lt_of_le`). Affine causal lines `timeLine p v` are inextensible causal curves
  (`inextensible_timeLine`), and every one through a point of an open `W` meets every Cauchy
  surface of `W` (`exists_mem_line_of_isCauchySurfaceOn`).
* **B. The null-line criterion** `isCauchySurface_graph_iff`: for `f` strictly contracting,
  `graph f` is a Cauchy surface of `𝐌ⁿ` (DEC-14) **iff it meets every null affine line**. The
  `⇐` proof is the past-ray compactness argument: `exists_ray_of_tendsto` (directions of
  `[y n, z]` accumulate, `y n.1 → −∞`), `bddBelow_fst_Jminus_inter` / `bddAbove_fst_Jplus_inter`
  (the hub step: `J∓(z) ∩ {±T ≥ 0}` has bounded time), then `Inextensible.reparam`, the time
  limits of `Static.lean` and the intermediate value theorem. **The hyperboloid is the standard
  failing example**, and exactly which null lines it misses is computed: the null line
  `r + sℓ` meets it iff `ℓ.1 · ⟨r | ℓ⟩ < 0` (`exists_mem_graph_hyperboloid_null_iff`; for
  `ℓ = (1, e)`, iff `⟪r.2, e⟫ < r.1`), iff the line enters the open future cone
  (`exists_mem_graph_hyperboloid_null_iff_isFutureTimelike`). So it misses, e.g., the null lines
  `s ↦ s(1, e)` through the vertex (`exists_nullLine_not_mem_graph_hyperboloid`, the boundary
  case), but also `(−1, 0) + s(1, e)`, which avoids the vertex; and the criterion re-proves it is
  not Cauchy (`not_isCauchySurface_graph_hyperboloid_of_criterion`, Achronal's statement on
  purpose).
* **C.** For an open `W` with an acausal Cauchy surface: `W` is causally convex
  (`segment_subset_of_isCauchySurfaceOn`: `[p, q] ⊆ W` and `p ≤_W q`); the **hub lemma**
  `isCompact_Jminus_inter_timeSub` (`J⁻(z) ∩ {T ≥ 0}` compact and inside `W`, `z ∈ W`, when
  `graph f` is a Cauchy surface of `W`) and its future twin `isCompact_Jplus_inter_timeSub`;
  **(CC′)** as `CCPrime` = `IsEntireAcausalGraph` + `NullSaturated` (`docs/BARBOT-WAVE3.md` §3),
  `isEntireAcausalGraph_iff` (= graph of a strictly contracting map, through Achronal's
  `exists_lipschitz_graph_iff`), and **its transfer** `ccPrime_of_isCauchySurfaceOn` between two
  Cauchy surfaces of one `W`. Inhabitants (kb/0011): the horizontal hyperplanes
  (`ccPrime_graph_const`) and **the hyperboloid** (`ccPrime_graph_hyperboloid`, via
  `nullSaturated_graph_hyperboloid`): (CC′) holds for a surface that is no Cauchy surface of
  `𝐌ⁿ`, as Cauchy-completeness should.
* **D.** `dependenceDomain C W S` for a general causality (inextensible curves of `W`);
  `graph_subset_interior_dependenceDomain` (`S ⊆ int D(S)` for strictly contracting `f`, by a
  cylinder argument); `dependenceDomain_eq_of_isCauchySurfaceOn`, so `D = 𝐌ⁿ` under the
  criterion (`dependenceDomain_graph_eq_univ`); **`D(hyperboloid) = {p |
  IsFutureTimelike p}`** (`dependenceDomain_hyperboloid`, `0 < d`), hence open.

## Hypothesis checklist

| paper / design hypothesis | here |
|---|---|
| [8.G] "contracting" | ✓ carried in its strict reading `IsStrictContraction` (↔ acausal, Barbot's `|x − y|² > 0`); the 1-Lipschitz reading where it suffices (`isTimeFunction_timeSub`, `timeSub_le_of_le`) |
| design B: `IsStrictContraction` stated with `dist` | ✓ carried with `‖x − y‖`, Achronal's form (`dist_eq_norm`) |
| design C `segment_subset_of_isCauchySurfaceOn`: `Σ ⊆ W` | ⚠ weakened: not needed |
| design C hub lemma: `lgraph f ⊆ W`, `0 ≤ T z` | ⚠ weakened: neither is needed (`T z < 0` makes the set empty) |
| design C (CC′) transfer | ✓ carried as designed (`S, S' ⊆ W`, both Cauchy surfaces of `W`) |
| design D `isOpen_dependenceDomain` (general) | not stated: openness is proved for the hyperboloid only; `interior` is used throughout, as the design's fallback says |
| Rem 2.2, any `n` | ⚠ strengthened: `0 < d` (`n ≥ 2`) for `dependenceDomain_hyperboloid`, `isOpen_dependenceDomain_hyperboloid` and `isCauchySurfaceOn_futureCone_hyperboloid`. For the first two it is needed: for `d = 0` the hyperboloid is the point `t = 1` and `D` is all of the line. For the third it is not (for `d = 0`, `Ω = {t > 0}` and `S = {t = 1}` is still Cauchy for `Ω`); it is inherited from the proof route through `D(S)`, and the `d = 0` case is not stated |
| Rem 2.2, "a connected component" `Ω` | ⚠ only the future component `{t > ‖x‖}`; the past one (`graph_neg_hyperboloid`) follows by time reflection and is not stated |

## SCOPE (disclosed)

* No b-label is certified: every passage is prose. The null-line criterion turns l.2491's "every
  nonspacelike line meets" into "is a Cauchy surface of `𝐌ⁿ`", and the hyperboloid shows that
  this fails for a strictly contracting entire graph (W7); nothing of `bprop:danom` is claimed.
* Rem 2.2 is treated for the future component of `{Q < 0}` only; the past component, the graph
  of `−hyperboloid` (Achronal's `graph_neg_hyperboloid`), follows by time reflection and is not
  stated. That the hyperboloid is a Cauchy surface of `Ω` (`isCauchySurfaceOn_futureCone_hyperboloid`)
  rests on the one `sorry` below.
* `isCauchySurfaceOn_interior_dependenceDomain` — `S` is a Cauchy surface of `int D(S)` — proves
  uniqueness and rests on **one** `sorry` for existence: a causal curve inextensible in `W =
  int D(S)` (not in `𝐌ⁿ`) has to be shown to meet `S`. The obstruction is the `W`-relative
  extension lemma (a past limit point inside `W` makes the curve extensible in `W`; the library
  has `pastExtensible_of_tendsto` and `Inextensible.reparam` for `⊤` only) together with
  `J⁻(y) ∩ {T ≥ 0} ⊆ int D(S)` for `y ∈ int D(S)`. Rem 2.2's first half,
  `isCauchySurfaceOn_futureCone_hyperboloid`, rests on it.
* The null lines of the criterion are all affine lines `{p + s v}` with `v ≠ 0`, `minkQ v = 0`,
  either time orientation; the Cauchy surface is DEC-14's (every inextensible causal curve, over
  any interval, meets it once).
* The norm on `Minkowski d` is the sup norm of the product (`Form.lean`); only `‖p.2‖` enters.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 3, package WP-32d-LipschitzGraph.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Metric

variable {d : ℕ}

/-! ### A. Graphs, their time function, strict contraction -/

/-- The time function `T = t − f(x)` of the graph of `f`: `graph f = T⁻¹(0)`. -/
def timeSub (f : EuclideanSpace ℝ (Fin d) → ℝ) (p : Minkowski d) : ℝ := p.1 - f p.2

/-- `f` is **strictly contracting**: `|f x − f y| < ‖x − y‖` for `x ≠ y` (Barbot's "contracting",
l.2308, in its strict reading; `isAcausal_graph_iff`). -/
def IsStrictContraction (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ x y, x ≠ y → |f x - f y| < ‖x - y‖

variable {f : EuclideanSpace ℝ (Fin d) → ℝ}

theorem timeSub_apply (p : Minkowski d) : timeSub f p = p.1 - f p.2 := rfl

theorem mem_graph_iff_timeSub {p : Minkowski d} : p ∈ graph f ↔ timeSub f p = 0 := by
  rw [mem_graph, timeSub, sub_eq_zero]

theorem isAcausal_graph_iff_isStrictContraction :
    (minkowski d).IsAcausal (graph f) ↔ IsStrictContraction f :=
  isAcausal_graph_iff

theorem IsStrictContraction.lipschitzWith (hf : IsStrictContraction f) : LipschitzWith 1 f :=
  isAchronal_graph_iff.1 (minkowski_isAchronal_of_isAcausal
    (isAcausal_graph_iff_isStrictContraction.2 hf))

theorem IsStrictContraction.neg (hf : IsStrictContraction f) :
    IsStrictContraction fun x => -f x := fun x y h => by
  rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]; exact hf x y h

theorem continuous_timeSub (hf : LipschitzWith 1 f) : Continuous (timeSub f) :=
  continuous_fst.sub (hf.continuous.comp continuous_snd)

theorem abs_sub_le_norm_of_lipschitzWith_one (hf : LipschitzWith 1 f)
    (x y : EuclideanSpace ℝ (Fin d)) : |f x - f y| ≤ ‖x - y‖ := by
  simpa using abs_sub_le_of_lipschitz hf x y

/-- **The time function `T = t − f`** (`defi:fonction_temps`, DEC-10) of an entire 1-Lipschitz
graph. -/
theorem isTimeFunction_timeSub (hf : LipschitzWith 1 f) :
    (minkowski d).IsTimeFunction (timeSub f) :=
  staticCausality.isTimeFunction_sub f fun x y => by
    simpa [dist_eq_norm] using abs_sub_le_norm_of_lipschitzWith_one hf x y

/-- `T` is non-decreasing along `≤`, when `f` is 1-Lipschitz. -/
theorem timeSub_le_of_le (hf : LipschitzWith 1 f) {x y : Minkowski d}
    (h : (minkowski d).le ⊤ x y) : timeSub f x ≤ timeSub f y := by
  have := graphTime_le_of_le hf h
  simp only [timeSub, NNReal.coe_one, sub_self, zero_mul] at this ⊢
  linarith

/-- `T` is **strictly** increasing along `≤`, when `f` is strictly contracting. -/
theorem timeSub_lt_of_le (hf : IsStrictContraction f) {x y : Minkowski d}
    (h : (minkowski d).le ⊤ x y) (hne : x ≠ y) : timeSub f x < timeSub f y := by
  have h1 := minkowski_le_top_iff.1 h
  simp only [timeSub]
  by_cases h2 : y.2 = x.2
  · have h3 : x.1 < y.1 := minkowski_time_strict.2 x y h hne
    rw [h2]; linarith
  · have h3 := hf y.2 x.2 h2
    linarith [le_abs_self (f y.2 - f x.2)]

/-! ### Affine lines of `𝐌ⁿ` as inextensible causal curves -/

private theorem norm_snd_le_fst {v : Minkowski d} (hv : IsFutureCausal v) : ‖v.2‖ ≤ v.1 :=
  (sq_le_sq₀ (norm_nonneg _) hv.1).1 (minkQ_le_zero_iff.1 hv.2)

private theorem fst_pos_of_ne {v : Minkowski d} (hv : IsFutureCausal v) (hv0 : v ≠ 0) :
    0 < v.1 :=
  lt_of_le_of_ne hv.1 fun h => hv0 (eq_zero_of_fst_eq_zero h.symm hv.2)

/-- `p ≤ q` in `𝐌ⁿ` iff `q − p` is future causal (`le_top_iff_minkQ`, restated). -/
private theorem le_top_add_smul (p : Minkowski d) {v : Minkowski d} (hv : IsFutureCausal v) {s s' : ℝ}
    (h : s ≤ s') : (minkowski d).le ⊤ (p + s • v) (p + s' • v) := by
  rw [le_top_iff_minkQ, show p + s' • v - (p + s • v) = (s' - s) • v by rw [sub_smul]; abel]
  refine ⟨?_, ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul]; exact mul_nonneg (sub_nonneg.2 h) hv.1
  · rw [minkQ_smul]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hv.2

/-- The affine line through `p` with direction `v`, parametrised by time (`v.1 > 0`). -/
noncomputable def timeLine (p v : Minkowski d) (τ : ℝ) : Minkowski d := p + ((τ - p.1) / v.1) • v

theorem timeLine_fst {p v : Minkowski d} (hv : 0 < v.1) (τ : ℝ) : (timeLine p v τ).1 = τ := by
  simp only [timeLine, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  field_simp; ring

theorem timeLine_param {p v : Minkowski d} (hv : 0 < v.1) (s : ℝ) :
    timeLine p v (p.1 + s * v.1) = p + s • v := by
  simp only [timeLine, add_sub_cancel_left, mul_div_assoc, div_self hv.ne', mul_one]

theorem timeLine_self {p v : Minkowski d} (hv : 0 < v.1) : timeLine p v p.1 = p := by
  simpa using timeLine_param hv 0

theorem timeLine_injective {p v : Minkowski d} (hv : 0 < v.1) : Function.Injective (timeLine p v) :=
  fun τ τ' h => by rw [← timeLine_fst hv τ, ← timeLine_fst hv τ', h]

theorem timeLine_eq_add_smul {p v : Minkowski d} (τ : ℝ) :
    timeLine p v τ = p + ((τ - p.1) / v.1) • v := rfl

theorem le_top_timeLine {p v : Minkowski d} (hv : IsFutureCausal v) (hv1 : 0 < v.1) {τ τ' : ℝ}
    (h : τ ≤ τ') : (minkowski d).le ⊤ (timeLine p v τ) (timeLine p v τ') :=
  le_top_add_smul p hv (div_le_div_of_nonneg_right (by linarith) hv1.le)

/-- **An affine causal line is an inextensible causal curve of `𝐌ⁿ`.** -/
theorem inextensible_timeLine (p : Minkowski d) {v : Minkowski d} (hv : IsFutureCausal v)
    (hv0 : v ≠ 0) : (minkowski d).Inextensible ⊤ univ (timeLine p v) := by
  have hv1 := fst_pos_of_ne hv hv0
  set γ : ℝ → EuclideanSpace ℝ (Fin d) := fun τ => p.2 + ((τ - p.1) / v.1) • v.2 with hγ
  have hc : timeLine p v = fun τ => (τ, γ τ) := by
    funext τ
    refine Prod.ext (timeLine_fst hv1 τ) ?_
    simp [timeLine, hγ]
  have hlip : ∀ a b, StaticCurve 1 ((⊤ : Opens (Minkowski d)) : Set (Minkowski d)) γ a b :=
    fun a b => ⟨fun τ _ τ' _ => by
      rw [dist_eq_norm]
      simp only [hγ, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
      rw [show (τ - p.1) / v.1 - (τ' - p.1) / v.1 = (τ - τ') / v.1 by ring, abs_div,
        abs_of_pos hv1, one_mul, div_mul_eq_mul_div, div_le_iff₀ hv1]
      exact mul_le_mul_of_nonneg_left (norm_snd_le_fst hv) (abs_nonneg _), fun _ _ => trivial⟩
  have hcurve : (minkowski d).CausalCurveIn ⊤ univ (timeLine p v) := by
    rw [hc]
    refine ⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ => ?_⟩
    rcases le_or_gt a b with hab | hab
    · exact staticCausality.causalCurveOn_graph (hlip a b)
    · exact CurveOn.of_lt hab
  refine Causality.inextensible_of_unbounded (f := Prod.fst)
    (fun x y h => by have := minkowski_le_top_iff.1 h; linarith [norm_nonneg (y.2 - x.2)])
    hcurve (fun b => ⟨b + 1, by rw [timeLine_fst hv1]; linarith⟩)
    (fun b => ⟨b - 1, by rw [timeLine_fst hv1]; linarith⟩)

/-! ### Lines and Cauchy surfaces of an open set -/

/-- The parameters of the component, in the open `W`, of a curve over `ℝ` through `t₀`. -/
private theorem exists_mem_component_of_isCauchySurfaceOn {W : Opens (Minkowski d)}
    {S : Set (Minkowski d)} (hC : (minkowski d).IsCauchySurfaceOn W S) {c : ℝ → Minkowski d}
    (hc : (minkowski d).Inextensible ⊤ univ c) {t₀ : ℝ} (ht₀ : c t₀ ∈ W) :
    ∃ t ∈ ordConnectedComponent (univ ∩ c ⁻¹' W) t₀, c t ∈ S := by
  obtain ⟨_, ⟨⟨t, ht, rfl⟩, hS⟩, -⟩ :=
    hC _ c (Causality.inextensible_ordConnectedComponent minkowski_isCausal hc (mem_univ t₀) ht₀)
  exact ⟨t, ht, hS⟩

/-- **Every causal line through a point of `W` meets a Cauchy surface of `W`.** -/
theorem exists_mem_line_of_isCauchySurfaceOn {W : Opens (Minkowski d)} {S : Set (Minkowski d)}
    (hC : (minkowski d).IsCauchySurfaceOn W S) {z v : Minkowski d} (hz : z ∈ W)
    (hv : IsFutureCausal v) (hv0 : v ≠ 0) : ∃ s : ℝ, z + s • v ∈ S := by
  have hv1 := fst_pos_of_ne hv hv0
  obtain ⟨t, -, ht⟩ := exists_mem_component_of_isCauchySurfaceOn hC (inextensible_timeLine z hv hv0)
    (t₀ := z.1) (by rw [timeLine_self hv1]; exact hz)
  exact ⟨_, ht⟩

/-! ### B. The ray argument and the null-line criterion -/

/-- **The compactness step of the ray argument.** If `y n ≤ z` with `(y n).1 → −∞`, the normalised
directions `(z − y n)/(z.1 − (y n).1)` accumulate on a future causal `v` with `v.1 = 1`, and the
past ray `z − s v`, `s ≥ 0`, lies in every closed set containing the segments `[y n, z]`. -/
theorem exists_ray_of_tendsto {F : Set (Minkowski d)} (hF : IsClosed F) {z : Minkowski d}
    {y : ℕ → Minkowski d} (hy : ∀ n, (minkowski d).le ⊤ (y n) z)
    (hseg : ∀ n, segment ℝ (y n) z ⊆ F) (ht : Tendsto (fun n => (y n).1) atTop atBot) :
    ∃ v : Minkowski d, IsFutureCausal v ∧ v.1 = 1 ∧ ∀ s : ℝ, 0 ≤ s → z - s • v ∈ F := by
  set K : Set (Minkowski d) := {v | v.1 = 1 ∧ ‖v.2‖ ≤ 1} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_eq continuous_fst continuous_const).inter
        (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)
    · refine isBounded_iff_forall_norm_le.2 ⟨1, fun v hv => ?_⟩
      rw [Prod.norm_def]
      refine max_le ?_ hv.2
      rw [hv.1, norm_one]
  set Δ : ℕ → ℝ := fun n => z.1 - (y n).1 with hΔ
  set w : ℕ → Minkowski d := fun n => if 0 < Δ n then (Δ n)⁻¹ • (z - y n) else (1, 0) with hw
  have hwK : ∀ n, w n ∈ K := by
    intro n
    by_cases h : 0 < Δ n
    · simp only [hw, if_pos h, hK, mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
        Prod.snd_sub, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h]
      refine ⟨inv_mul_cancel₀ h.ne', ?_⟩
      rw [inv_mul_le_iff₀ h, mul_one]
      exact minkowski_le_top_iff.1 (hy n)
    · simp only [hw, if_neg h, hK, mem_setOf_eq]
      simp
  obtain ⟨v, hvK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hwK
  have hΔφ : Tendsto (fun n => Δ (φ n)) atTop atTop := by
    have : Tendsto Δ atTop atTop := by
      refine (tendsto_atTop_add_const_left _ z.1 (tendsto_neg_atBot_atTop.comp ht)).congr
        fun n => ?_
      simp [hΔ, sub_eq_add_neg]
    exact this.comp hφ.tendsto_atTop
  refine ⟨v, ⟨by rw [hvK.1]; exact zero_le_one, ?_⟩, hvK.1, fun s hs => ?_⟩
  · rw [minkQ, hvK.1]
    nlinarith [hvK.2, norm_nonneg v.2]
  have hconv : Tendsto (fun n => z - s • w (φ n)) atTop (𝓝 (z - s • v)) :=
    tendsto_const_nhds.sub (hlim.const_smul s)
  refine hF.mem_of_tendsto hconv ?_
  filter_upwards [hΔφ.eventually_ge_atTop (s + 1)] with n hn
  have hpos : 0 < Δ (φ n) := by linarith
  simp only [hw, if_pos hpos]
  refine hseg (φ n) ?_
  rw [segment_eq_image']
  refine ⟨1 - s / Δ (φ n), ⟨?_, ?_⟩, ?_⟩
  · rw [sub_nonneg, div_le_one hpos]; linarith
  · linarith [div_nonneg hs hpos.le]
  · show y (φ n) + (1 - s / Δ (φ n)) • (z - y (φ n)) = z - s • (Δ (φ n))⁻¹ • (z - y (φ n))
    rw [sub_smul, one_smul, smul_smul, div_eq_mul_inv]
    abel

/-- A strictly contracting graph cannot be met by a causal line `p + s v` (`v ≠ 0`) at a parameter
`s` with `T ≥ 0` at `s − 1`. -/
private theorem false_of_mem_line (hf : IsStrictContraction f) {p v : Minkowski d}
    (hv : IsFutureCausal v) (hv0 : v ≠ 0) {s : ℝ} (hs : p + s • v ∈ graph f)
    (hT : 0 ≤ timeSub f (p + (s - 1) • v)) : False := by
  have hle := le_top_add_smul p hv (show s - 1 ≤ s by linarith)
  have hne : p + (s - 1) • v ≠ p + s • v := by
    intro h
    have : (s - 1) • v = s • v := add_left_cancel h
    rw [sub_smul, one_smul, sub_eq_self] at this
    exact hv0 this
  have := timeSub_lt_of_le hf hle hne
  rw [mem_graph_iff_timeSub.1 hs] at this
  linarith

/-- **The hub step.** Let `f` be strictly contracting and `z` a point every causal line through
which meets `graph f`. Then the points of `J⁻(z)` with `T ≥ 0` have time bounded below. -/
theorem bddBelow_fst_Jminus_inter (hf : IsStrictContraction f) {z : Minkowski d}
    (hmeet : ∀ v : Minkowski d, IsFutureCausal v → v ≠ 0 → ∃ s : ℝ, z + s • v ∈ graph f) :
    BddBelow (Prod.fst '' ((minkowski d).Jminus ⊤ {z} ∩ {q | 0 ≤ timeSub f q})) := by
  by_contra hbdd
  rw [not_bddBelow_iff] at hbdd
  have hex : ∀ n : ℕ, ∃ q, (minkowski d).le ⊤ q z ∧ 0 ≤ timeSub f q ∧ q.1 < -(n : ℝ) := by
    intro n
    obtain ⟨_, ⟨q, ⟨hq1, hq2⟩, rfl⟩, hlt⟩ := hbdd (-(n : ℝ))
    exact ⟨q, by simpa using hq1, hq2, hlt⟩
  choose y hyz hyT hyt using hex
  have hlip := hf.lipschitzWith
  have hF : IsClosed {q : Minkowski d | 0 ≤ timeSub f q} :=
    isClosed_le continuous_const (continuous_timeSub hlip)
  have hseg : ∀ n, segment ℝ (y n) z ⊆ {q | 0 ≤ timeSub f q} := by
    intro n q hq
    rw [segment_eq_image'] at hq
    obtain ⟨θ, hθ, rfl⟩ := hq
    have hzy : IsFutureCausal (z - y n) := le_top_iff_minkQ.1 (hyz n)
    have := le_top_add_smul (y n) hzy hθ.1
    rw [zero_smul, add_zero] at this
    exact (hyT n).trans (timeSub_le_of_le hlip this)
  have ht : Tendsto (fun n => (y n).1) atTop atBot :=
    tendsto_atBot_mono (fun n => (hyt n).le) (tendsto_neg_atTop_atBot.comp
      tendsto_natCast_atTop_atTop)
  obtain ⟨v, hv, hv1, hray⟩ := exists_ray_of_tendsto hF hyz hseg ht
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv1; simp at hv1
  have hTz : 0 ≤ timeSub f z := (hyT 0).trans (timeSub_le_of_le hlip (hyz 0))
  have hline : ∀ r : ℝ, 0 ≤ timeSub f (z + r • v) := by
    intro r
    rcases le_total r 0 with hr | hr
    · have := hray (-r) (by linarith)
      rwa [neg_smul, sub_neg_eq_add] at this
    · have := le_top_add_smul z hv hr
      rw [zero_smul, add_zero] at this
      exact hTz.trans (timeSub_le_of_le hlip this)
  obtain ⟨s, hs⟩ := hmeet v hv hv0
  exact false_of_mem_line hf hv hv0 hs (hline _)

/-- The time reflection `(t, x) ↦ (−t, x)`. -/
private def refl (p : Minkowski d) : Minkowski d := (-p.1, p.2)

private theorem le_refl_iff {p q : Minkowski d} :
    (minkowski d).le ⊤ (refl q) (refl p) ↔ (minkowski d).le ⊤ p q := by
  simp only [minkowski_le_top_iff, refl]
  rw [norm_sub_rev]; ring_nf

private theorem timeSub_neg_refl (p : Minkowski d) :
    timeSub (fun x => -f x) (refl p) = -timeSub f p := by
  simp [timeSub, refl]; ring

/-- **The hub step, future side**, by time reflection. -/
theorem bddAbove_fst_Jplus_inter (hf : IsStrictContraction f) {z : Minkowski d}
    (hmeet : ∀ v : Minkowski d, IsFutureCausal v → v ≠ 0 → ∃ s : ℝ, z + s • v ∈ graph f) :
    BddAbove (Prod.fst '' ((minkowski d).Jplus ⊤ {z} ∩ {q | timeSub f q ≤ 0})) := by
  have hmeet' : ∀ v : Minkowski d, IsFutureCausal v → v ≠ 0 →
      ∃ s : ℝ, refl z + s • v ∈ graph fun x => -f x := by
    intro v hv hv0
    have hw : IsFutureCausal ((v.1, -v.2) : Minkowski d) := ⟨hv.1, by simpa [minkQ] using hv.2⟩
    have hw0 : ((v.1, -v.2) : Minkowski d) ≠ 0 := fun h => hv0 (Prod.ext (by
      simpa using congrArg Prod.fst h) (by simpa using congrArg Prod.snd h))
    obtain ⟨s, hs⟩ := hmeet _ hw hw0
    refine ⟨-s, ?_⟩
    simp only [mem_graph, refl, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, smul_neg] at hs ⊢
    rw [neg_smul, ← hs]
    ring
  obtain ⟨b, hb⟩ := bddBelow_fst_Jminus_inter hf.neg hmeet'
  refine ⟨-b, ?_⟩
  rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
  have : refl q ∈ (minkowski d).Jminus ⊤ {refl z} ∩ {q | 0 ≤ timeSub (fun x => -f x) q} := by
    refine ⟨?_, ?_⟩
    · rw [Precausality.mem_Jminus_singleton, le_refl_iff]
      simpa using hq1
    · show 0 ≤ timeSub (fun x => -f x) (refl q)
      rw [timeSub_neg_refl]; simpa using hq2
  have := hb ⟨_, this, rfl⟩
  simp only [refl] at this
  linarith

/-- On an inextensible curve over `ℝ` through `z`, a point before `z` with `T ≤ 0`, when the
hub step holds at `z`. -/
private theorem exists_timeSub_nonpos (hf : IsStrictContraction f) {g : ℝ → Minkowski d}
    (hg : (minkowski d).Inextensible ⊤ univ g) {t₀ : ℝ}
    (hmeet : ∀ v : Minkowski d, IsFutureCausal v → v ≠ 0 → ∃ s : ℝ, g t₀ + s • v ∈ graph f) :
    ∃ s ≤ t₀, timeSub f (g s) ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨b, hb⟩ := bddBelow_fst_Jminus_inter hf hmeet
  have ht : Tendsto (fun n : ℕ => (g (t₀ - n)).1) atTop atBot :=
    (staticCausality.tendsto_time_atBot hg).comp
      (tendsto_atBot_add_const_left _ t₀ (tendsto_neg_atTop_atBot.comp
        tendsto_natCast_atTop_atTop) |>.congr fun n => by simp [sub_eq_add_neg])
  obtain ⟨n, hn⟩ := (ht.eventually_lt_atBot b).exists
  have hle : (minkowski d).le ⊤ (g (t₀ - n)) (g t₀) :=
    hg.1.le_of_le trivial trivial (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have := hb ⟨g (t₀ - n), ⟨by simpa using hle,
    (h _ (by linarith [Nat.cast_nonneg (α := ℝ) n])).le⟩, rfl⟩
  linarith

/-- The future side of `exists_timeSub_nonpos`. -/
private theorem exists_timeSub_nonneg (hf : IsStrictContraction f) {g : ℝ → Minkowski d}
    (hg : (minkowski d).Inextensible ⊤ univ g) {t₀ : ℝ}
    (hmeet : ∀ v : Minkowski d, IsFutureCausal v → v ≠ 0 → ∃ s : ℝ, g t₀ + s • v ∈ graph f) :
    ∃ s, t₀ ≤ s ∧ 0 ≤ timeSub f (g s) := by
  by_contra h
  push Not at h
  obtain ⟨b, hb⟩ := bddAbove_fst_Jplus_inter hf hmeet
  have ht : Tendsto (fun n : ℕ => (g (t₀ + n)).1) atTop atTop :=
    (staticCausality.tendsto_time_atTop hg).comp
      (tendsto_atTop_add_const_left _ t₀ tendsto_natCast_atTop_atTop)
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop b).exists
  have hle : (minkowski d).le ⊤ (g t₀) (g (t₀ + n)) :=
    hg.1.le_of_le trivial trivial (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have := hb ⟨g (t₀ + n), ⟨by simpa using hle,
    (h _ (by linarith [Nat.cast_nonneg (α := ℝ) n])).le⟩, rfl⟩
  linarith

/-- **The intermediate value step.** An inextensible causal curve of `𝐌ⁿ` (over any interval)
meets `graph f` as soon as, after reparametrisation over `ℝ`, `T = t − f` takes a value `≤ 0` and
a value `≥ 0` on it. -/
private theorem exists_mem_graph_of_reparam (hf : LipschitzWith 1 f) {I : Set ℝ}
    {c : ℝ → Minkowski d} (hc : (minkowski d).Inextensible ⊤ I c)
    (h : ∀ g : ℝ → Minkowski d, (minkowski d).Inextensible ⊤ univ g → range g = c '' I →
      (∃ s, timeSub f (g s) ≤ 0) ∧ ∃ s, 0 ≤ timeSub f (g s)) :
    (c '' I ∩ graph f).Nonempty := by
  obtain ⟨ψ, -, -, hψr, hcψ⟩ := hc.reparam minkowski_causallyArcConnected minkowski_isCausal
    staticCausality.Jminus_ne_singleton staticCausality.Jplus_ne_singleton
  have hr : range (c ∘ ψ) = c '' I := by rw [range_comp, hψr]
  obtain ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩ := h _ hcψ hr
  have hcont : Continuous (timeSub f ∘ (c ∘ ψ)) :=
    (continuous_timeSub hf).comp hcψ.1.continuous
  obtain ⟨s, hs⟩ := intermediate_value_univ s₁ s₂ hcont ⟨hs₁, hs₂⟩
  exact ⟨c (ψ s), hr ▸ mem_range_self s, mem_graph_iff_timeSub.2 hs⟩

/-- An acausal set meets a causal curve at most once. -/
private theorem unique_of_isAcausal {S : Set (Minkowski d)} (hS : (minkowski d).IsAcausal S)
    {I : Set ℝ} {c : ℝ → Minkowski d} (hc : (minkowski d).CausalCurveIn ⊤ I c) {x y : Minkowski d}
    (hx : x ∈ c '' I ∩ S) (hy : y ∈ c '' I ∩ S) : x = y := by
  obtain ⟨⟨t, ht, rfl⟩, hxS⟩ := hx
  obtain ⟨⟨t', ht', rfl⟩, hyS⟩ := hy
  rcases le_total t t' with h | h
  · exact hS _ hxS _ hyS (hc.le_of_le ht ht' h)
  · exact (hS _ hyS _ hxS (hc.le_of_le ht' ht h)).symm

/-- Every causal line meets an entire 1-Lipschitz graph meeting every null line. -/
private theorem forall_line_of_null (hf : LipschitzWith 1 f)
    (hnull : ∀ p v : Minkowski d, v ≠ 0 → minkQ v = 0 → ∃ s : ℝ, p + s • v ∈ graph f)
    (z v : Minkowski d) (hv : IsFutureCausal v) (hv0 : v ≠ 0) : ∃ s : ℝ, z + s • v ∈ graph f := by
  rcases hv.2.lt_or_eq with h | h
  · exact (existsUnique_mem_graph_line hf z ⟨fst_pos_of_ne hv hv0, h⟩).exists
  · exact hnull z v hv0 h

/-- **The null-line criterion** (`docs/BARBOT-WAVE3.md` §1B; the "nonspacelike line" sentence of
`bprop:danom`, l.2489–2491). For `f` strictly contracting, `graph f` is a Cauchy surface of `𝐌ⁿ`
iff it meets every null affine line. The timelike lines it meets anyway
(`existsUnique_mem_graph_line`). -/
theorem isCauchySurface_graph_iff (hf : IsStrictContraction f) :
    (minkowski d).IsCauchySurface (graph f) ↔
      ∀ p v : Minkowski d, v ≠ 0 → minkQ v = 0 → ∃ s : ℝ, p + s • v ∈ graph f := by
  constructor
  · intro hS p v hv0 hq
    have hv1 : v.1 ≠ 0 := fun h => hv0 (eq_zero_of_fst_eq_zero h hq.le)
    rcases lt_or_gt_of_ne hv1 with h | h
    · obtain ⟨s, hs⟩ := exists_mem_line_of_isCauchySurfaceOn hS (W := ⊤) (z := p) trivial
        (v := -v) ⟨by simp; linarith, by simpa using hq.le⟩ (neg_ne_zero.2 hv0)
      exact ⟨-s, by rwa [neg_smul, ← smul_neg]⟩
    · exact exists_mem_line_of_isCauchySurfaceOn hS (W := ⊤) (z := p) trivial
        ⟨h.le, hq.le⟩ hv0
  · intro hnull I c hc
    have hall := forall_line_of_null hf.lipschitzWith hnull
    obtain ⟨x, hx⟩ := exists_mem_graph_of_reparam hf.lipschitzWith hc fun g hg _ => by
      obtain ⟨s₁, -, h₁⟩ := exists_timeSub_nonpos hf hg (t₀ := 0) (hall _)
      obtain ⟨s₂, -, h₂⟩ := exists_timeSub_nonneg hf hg (t₀ := 0) (hall _)
      exact ⟨⟨s₁, h₁⟩, ⟨s₂, h₂⟩⟩
    exact ⟨x, hx, fun y hy => unique_of_isAcausal (isAcausal_graph_iff_isStrictContraction.2 hf)
      hc.1 hy hx⟩

/-- **Rem 2.2's hyperboloid is the standard failing example of the criterion.** It is strictly
contracting (`abs_hyperboloid_sub_lt`), and for `0 < d` it misses the null line `s ↦ s(1, e)`
through the vertex `0` of its asymptotic cone. This is one missed line, the boundary case: the
exact set of missed null lines is `exists_mem_graph_hyperboloid_null_iff`. -/
theorem exists_nullLine_not_mem_graph_hyperboloid (hd : 0 < d) :
    IsStrictContraction (hyperboloid d) ∧ ∃ v : Minkowski d, v ≠ 0 ∧ minkQ v = 0 ∧
      ∀ s : ℝ, (0 : Minkowski d) + s • v ∉ graph (hyperboloid d) := by
  refine ⟨fun _ _ h => abs_hyperboloid_sub_lt h, (1, unitVec d hd), fun h => by
    simpa using congrArg Prod.fst h, by simp [minkQ, norm_unitVec], fun s hs => ?_⟩
  rw [zero_add, mem_graph] at hs
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, hyperboloid, norm_smul,
    norm_unitVec, Real.norm_eq_abs, sq_abs] at hs
  exact (ne_of_lt ((le_abs_self s).trans_lt (abs_lt_sqrt_one_add_sq s))) hs

/-- Achronal's `not_isCauchySurface_graph_hyperboloid`, restated **on purpose** as a corollary of
the null-line criterion (`isCauchySurface_graph_iff`): the criterion's standard failing example. -/
theorem not_isCauchySurface_graph_hyperboloid_of_criterion (hd : 0 < d) :
    ¬ (minkowski d).IsCauchySurface (graph (hyperboloid d)) := by
  obtain ⟨hf, v, hv0, hv, hmiss⟩ := exists_nullLine_not_mem_graph_hyperboloid hd
  rw [isCauchySurface_graph_iff hf]
  intro h
  obtain ⟨s, hs⟩ := h 0 v hv0 hv
  exact hmiss s hs

/-- **Exactly which null lines the hyperboloid meets.** The null line `r + sℓ` (`ℓ ≠ 0`,
`minkQ ℓ = 0`) meets `graph hyperboloid` iff `ℓ.1 · ⟨r | ℓ⟩ < 0`; for `ℓ = (1, e)`, `‖e‖ = 1`,
iff `⟪r.2, e⟫ < r.1`. The condition depends on `r` only through `⟨r | ℓ⟩`, constant on each null
hyperplane `ℓ^⊥ + r` (`nullSaturated_graph_hyperboloid`). Algebra: on the line, squaring the
graph equation leaves the linear equation `−2s⟨r | ℓ⟩ = 1 + ‖r.2‖² − r.1²`, and the sign of the
time `r.1 + sℓ.1` of its solution is that of `ℓ.1 · (−⟨r | ℓ⟩)`, by Cauchy–Schwarz. -/
theorem exists_mem_graph_hyperboloid_null_iff {r ℓ : Minkowski d} (hℓ0 : ℓ ≠ 0)
    (hℓ : minkQ ℓ = 0) :
    (∃ s : ℝ, r + s • ℓ ∈ graph (hyperboloid d)) ↔ ℓ.1 * minkB r ℓ < 0 := by
  have ha : ℓ.1 ≠ 0 := fun h => hℓ0 (eq_zero_of_fst_eq_zero h hℓ.le)
  have hw : ‖ℓ.2‖ ^ 2 = ℓ.1 ^ 2 := by have := hℓ; simp only [minkQ] at this; linarith
  have hB : minkB r ℓ = -(r.1 * ℓ.1) + inner ℝ r.2 ℓ.2 := rfl
  have hcs : inner ℝ r.2 ℓ.2 ^ 2 ≤ ‖r.2‖ ^ 2 * ℓ.1 ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm r.2 ℓ.2) 2
    rwa [sq_abs, mul_pow, hw] at h1
  have hexp : ∀ s : ℝ, ‖r.2 + s • ℓ.2‖ ^ 2 =
      ‖r.2‖ ^ 2 + 2 * s * inner ℝ r.2 ℓ.2 + s ^ 2 * ℓ.1 ^ 2 := fun s => by
    rw [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hw,
      real_inner_smul_right]
    ring
  have hmem : ∀ s : ℝ, r + s • ℓ ∈ graph (hyperboloid d) ↔
      0 ≤ r.1 + s * ℓ.1 ∧ (r.1 + s * ℓ.1) ^ 2 = 1 + ‖r.2 + s • ℓ.2‖ ^ 2 := fun s => by
    rw [mem_graph]
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
      hyperboloid]
    constructor
    · intro h; rw [h]; exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (by positivity)⟩
    · rintro ⟨h0, h⟩; rw [← h, Real.sqrt_sq h0]
  have hK : 0 < ℓ.1 * (ℓ.1 * r.1 ^ 2 - 2 * r.1 * inner ℝ r.2 ℓ.2 + ℓ.1 * ‖r.2‖ ^ 2 + ℓ.1) := by
    have ha2 : 0 < ℓ.1 ^ 2 := by positivity
    have : ℓ.1 * (ℓ.1 * r.1 ^ 2 - 2 * r.1 * inner ℝ r.2 ℓ.2 + ℓ.1 * ‖r.2‖ ^ 2 + ℓ.1) =
        (ℓ.1 * r.1 - inner ℝ r.2 ℓ.2) ^ 2 + (‖r.2‖ ^ 2 * ℓ.1 ^ 2 - inner ℝ r.2 ℓ.2 ^ 2) +
          ℓ.1 ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg (ℓ.1 * r.1 - inner ℝ r.2 ℓ.2)]
  rw [hB]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨h0, h⟩ := (hmem s).1 hs
    have hX : 0 < r.1 + s * ℓ.1 := by
      rcases h0.lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0] at h; nlinarith [sq_nonneg ‖r.2 + s • ℓ.2‖]
    rw [hexp] at h
    have hKX : ℓ.1 * r.1 ^ 2 - 2 * r.1 * inner ℝ r.2 ℓ.2 + ℓ.1 * ‖r.2‖ ^ 2 + ℓ.1 =
        -2 * (-(r.1 * ℓ.1) + inner ℝ r.2 ℓ.2) * (r.1 + s * ℓ.1) := by
      linear_combination (-ℓ.1) * h
    rw [hKX] at hK
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hc hX.le]
  · intro hab
    have hB0 : -(r.1 * ℓ.1) + inner ℝ r.2 ℓ.2 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hab; exact lt_irrefl _ hab
    set B := -(r.1 * ℓ.1) + inner ℝ r.2 ℓ.2 with hBdef
    set s := -(1 + ‖r.2‖ ^ 2 - r.1 ^ 2) / (2 * B) with hsdef
    have hs : -2 * s * B = 1 + ‖r.2‖ ^ 2 - r.1 ^ 2 := by
      rw [hsdef]; field_simp
    have hKX : ℓ.1 * r.1 ^ 2 - 2 * r.1 * inner ℝ r.2 ℓ.2 + ℓ.1 * ‖r.2‖ ^ 2 + ℓ.1 =
        -2 * B * (r.1 + s * ℓ.1) := by
      rw [hBdef]; linear_combination (-ℓ.1) * hs
    have hX : 0 < r.1 + s * ℓ.1 := by
      rw [hKX] at hK
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hab.le hc]
    refine ⟨s, (hmem s).2 ⟨hX.le, ?_⟩⟩
    rw [hexp]
    rw [hBdef] at hs
    linear_combination hs

/-! ### C. Cauchy surfaces of an open `W ⊆ 𝐌ⁿ` -/

/-- **An open set with an acausal Cauchy surface is causally convex**: if `p, q ∈ W` and
`p ≤ q` in `𝐌ⁿ`, the segment `[p, q]` lies in `W` and `p ≤_W q`. -/
theorem segment_subset_of_isCauchySurfaceOn {W : Opens (Minkowski d)} {S : Set (Minkowski d)}
    (hac : (minkowski d).IsAcausal S) (hC : (minkowski d).IsCauchySurfaceOn W S)
    {p q : Minkowski d} (hp : p ∈ W) (hq : q ∈ W) (hpq : (minkowski d).le ⊤ p q) :
    segment ℝ p q ⊆ W ∧ (minkowski d).le W p q := by
  by_cases hpq' : p = q
  · subst hpq'
    rw [segment_same]
    exact ⟨singleton_subset_iff.2 hp, (minkowski d).le_refl hp⟩
  set v := q - p with hvdef
  have hv : IsFutureCausal v := le_top_iff_minkQ.1 hpq
  have hv0 : v ≠ 0 := sub_ne_zero.2 (Ne.symm hpq')
  have hv1 := fst_pos_of_ne hv hv0
  set c := timeLine p v with hcdef
  have hc := inextensible_timeLine p hv hv0
  have hcp : c p.1 = p := timeLine_self hv1
  have hqv : q.1 = p.1 + 1 * v.1 := by simp [hvdef]
  have hcq : c q.1 = q := by rw [hqv, hcdef, timeLine_param hv1, one_smul, hvdef]; abel
  obtain ⟨t₁, ht₁, hS₁⟩ := exists_mem_component_of_isCauchySurfaceOn hC hc (t₀ := p.1)
    (show c p.1 ∈ W by rw [hcp]; exact hp)
  obtain ⟨t₂, ht₂, hS₂⟩ := exists_mem_component_of_isCauchySurfaceOn hC hc (t₀ := q.1)
    (show c q.1 ∈ W by rw [hcq]; exact hq)
  have h12 : t₁ = t₂ := by
    apply timeLine_injective hv1
    rcases le_total t₁ t₂ with h | h
    · exact hac _ hS₁ _ hS₂ (le_top_timeLine hv hv1 h)
    · exact (hac _ hS₂ _ hS₁ (le_top_timeLine hv hv1 h)).symm
  rw [mem_ordConnectedComponent] at ht₁ ht₂
  rw [← h12] at ht₂
  have hpq1 : p.1 ≤ q.1 := by rw [hqv]; linarith
  have hIcc : ∀ τ ∈ Icc p.1 q.1, c τ ∈ W := fun τ hτ => by
    have : τ ∈ uIcc p.1 q.1 := by rw [uIcc_of_le hpq1]; exact hτ
    rcases uIcc_subset_uIcc_union_uIcc this with h | h
    · exact (ht₁ h).2
    · rw [uIcc_comm] at h; exact (ht₂ h).2
  refine ⟨?_, ?_⟩
  · rw [segment_eq_image']
    rintro _ ⟨θ, hθ, rfl⟩
    have := hIcc (p.1 + θ * v.1) ⟨by nlinarith [hθ.1], by rw [hqv]; nlinarith [hθ.2]⟩
    rwa [hcdef, timeLine_param hv1] at this
  · have hcW : (minkowski d).CausalCurveOn W c p.1 q.1 :=
      CurveOn.restrict (hc.1.curve p.1 trivial q.1 trivial) le_rfl le_rfl le_top hIcc
    have := hcW.le_of_le le_rfl hpq1 le_rfl
    rwa [hcp, hcq] at this

/-- `T < 0` strictly before a point of `graph f` on a line, when `f` is strictly contracting. -/
private theorem timeSub_neg_of_lt (hf : IsStrictContraction f) {p v : Minkowski d}
    (hv : IsFutureCausal v) (hv1 : 0 < v.1) {τ t : ℝ} (hτt : τ < t)
    (ht : timeLine p v t ∈ graph f) : timeSub f (timeLine p v τ) < 0 := by
  have := timeSub_lt_of_le hf (le_top_timeLine (p := p) hv hv1 hτt.le)
    fun h => hτt.ne (timeLine_injective hv1 h)
  rwa [mem_graph_iff_timeSub.1 ht] at this

/-- **The hub lemma** (`docs/BARBOT-WAVE3.md` §1C). Let `f` be strictly contracting and `graph f`
a Cauchy surface of the open `W`. For `z ∈ W`, `J⁻(z) ∩ {T ≥ 0}` is compact and lies in `W`. -/
theorem isCompact_Jminus_inter_timeSub {W : Opens (Minkowski d)} (hf : IsStrictContraction f)
    (hC : (minkowski d).IsCauchySurfaceOn W (graph f)) {z : Minkowski d} (hz : z ∈ W) :
    IsCompact ((minkowski d).Jminus ⊤ {z} ∩ {q | 0 ≤ timeSub f q}) ∧
      (minkowski d).Jminus ⊤ {z} ∩ {q | 0 ≤ timeSub f q} ⊆ W := by
  have hlip := hf.lipschitzWith
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := bddBelow_fst_Jminus_inter hf
      fun v hv hv0 => exists_mem_line_of_isCauchySurfaceOn hC hz hv hv0
    refine Metric.isCompact_of_isClosed_isBounded
      ((staticCausality.isClosed_Jminus_top z).inter
        (isClosed_le continuous_const (continuous_timeSub hlip)))
      ((isBounded_closedBall (x := z) (r := z.1 - b)).subset fun q hq => ?_)
    have h1 := hb ⟨q, hq, rfl⟩
    have h2 := minkowski_le_top_iff.1 (Precausality.mem_Jminus_singleton.1 hq.1)
    rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, dist_eq_norm, norm_sub_rev,
      abs_of_nonpos (by linarith [norm_nonneg (z.2 - q.2)])]
    exact max_le (by linarith) (by linarith)
  · rintro q ⟨hq1, hq2⟩
    by_contra hqW
    have hqz := Precausality.mem_Jminus_singleton.1 hq1
    have hne : q ≠ z := fun h => hqW (h ▸ hz)
    set v := z - q with hvdef
    have hv : IsFutureCausal v := le_top_iff_minkQ.1 hqz
    have hv0 : v ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hv1 := fst_pos_of_ne hv hv0
    have hzv : z.1 = q.1 + 1 * v.1 := by simp [hvdef]
    have hcz : timeLine q v z.1 = z := by
      rw [hzv, timeLine_param hv1, one_smul, hvdef]; abel
    obtain ⟨t, ht, hS⟩ := exists_mem_component_of_isCauchySurfaceOn hC
      (inextensible_timeLine q hv hv0) (t₀ := z.1) (by rw [hcz]; exact hz)
    rw [mem_ordConnectedComponent] at ht
    have hqt : q.1 < t := by
      by_contra hle
      have hmem : q.1 ∈ uIcc z.1 t := by
        rw [uIcc_comm, uIcc_of_le (show t ≤ z.1 by rw [hzv]; linarith)]
        exact ⟨not_lt.1 hle, by rw [hzv]; linarith⟩
      have := (ht hmem).2
      rw [mem_preimage, timeLine_self hv1] at this
      exact hqW this
    have := timeSub_neg_of_lt hf hv hv1 hqt hS
    rw [timeLine_self hv1] at this
    exact absurd hq2 (not_le.2 this)

/-- **The hub lemma, future side**: `J⁺(z) ∩ {T ≤ 0}` is compact and lies in `W`. -/
theorem isCompact_Jplus_inter_timeSub {W : Opens (Minkowski d)} (hf : IsStrictContraction f)
    (hC : (minkowski d).IsCauchySurfaceOn W (graph f)) {z : Minkowski d} (hz : z ∈ W) :
    IsCompact ((minkowski d).Jplus ⊤ {z} ∩ {q | timeSub f q ≤ 0}) ∧
      (minkowski d).Jplus ⊤ {z} ∩ {q | timeSub f q ≤ 0} ⊆ W := by
  have hlip := hf.lipschitzWith
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := bddAbove_fst_Jplus_inter hf
      fun v hv hv0 => exists_mem_line_of_isCauchySurfaceOn hC hz hv hv0
    refine Metric.isCompact_of_isClosed_isBounded
      ((staticCausality.isClosed_Jplus_top z).inter
        (isClosed_le (continuous_timeSub hlip) continuous_const))
      ((isBounded_closedBall (x := z) (r := b - z.1)).subset fun q hq => ?_)
    have h1 := hb ⟨q, hq, rfl⟩
    have h2 := minkowski_le_top_iff.1 (Precausality.mem_Jplus_singleton.1 hq.1)
    rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, dist_eq_norm,
      abs_of_nonneg (by linarith [norm_nonneg (q.2 - z.2)])]
    exact max_le (by linarith) (by linarith)
  · rintro q ⟨hq1, hq2⟩
    by_contra hqW
    have hzq := Precausality.mem_Jplus_singleton.1 hq1
    have hne : z ≠ q := fun h => hqW (h ▸ hz)
    set v := q - z with hvdef
    have hv : IsFutureCausal v := le_top_iff_minkQ.1 hzq
    have hv0 : v ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hv1 := fst_pos_of_ne hv hv0
    have hqv : q.1 = z.1 + 1 * v.1 := by simp [hvdef]
    have hcq : timeLine z v q.1 = q := by
      rw [hqv, timeLine_param hv1, one_smul, hvdef]; abel
    obtain ⟨t, ht, hS⟩ := exists_mem_component_of_isCauchySurfaceOn hC
      (inextensible_timeLine z hv hv0) (t₀ := z.1) (by rw [timeLine_self hv1]; exact hz)
    rw [mem_ordConnectedComponent] at ht
    have htq : t < q.1 := by
      by_contra hle
      have hmem : q.1 ∈ uIcc z.1 t := by
        rw [uIcc_of_le (show z.1 ≤ t by rw [hqv] at hle; linarith)]
        exact ⟨by rw [hqv]; linarith, not_lt.1 hle⟩
      have := (ht hmem).2
      rw [mem_preimage, hcq] at this
      exact hqW this
    have := timeSub_lt_of_le hf (le_top_timeLine (p := z) hv hv1 htq.le)
      fun h => htq.ne (timeLine_injective hv1 h)
    rw [mem_graph_iff_timeSub.1 hS, hcq] at this
    exact absurd hq2 (not_le.2 this)

/-! ### (CC′), and its transfer between two Cauchy surfaces of one `W` -/

/-- (CC′)(a) (`docs/BARBOT.md`, `docs/BARBOT-WAVE3.md` §3): `S` is acausal and meets every
timelike affine line. -/
structure IsEntireAcausalGraph (S : Set (Minkowski d)) : Prop where
  acausal : (minkowski d).IsAcausal S
  meets : ∀ p v : Minkowski d, IsFutureTimelike v → ∃ s : ℝ, p + s • v ∈ S

/-- (CC′)(b): a lightlike affine hyperplane `P = {x | ⟨x − p | ℓ⟩ = 0}` (`ℓ ≠ 0` null) meeting `S`
has each of its `ℓ`-lines meeting `S`. -/
def NullSaturated (S : Set (Minkowski d)) : Prop :=
  ∀ p ℓ : Minkowski d, ℓ ≠ 0 → minkQ ℓ = 0 → (∃ q ∈ S, minkB (q - p) ℓ = 0) →
    ∀ r, minkB (r - p) ℓ = 0 → ∃ s : ℝ, r + s • ℓ ∈ S

/-- **(CC′)**, the topological form of Cauchy-completeness (DEC-35). -/
structure CCPrime (S : Set (Minkowski d)) : Prop where
  entire : IsEntireAcausalGraph S
  nullSat : NullSaturated S

/-- (CC′)(a) is the graph of a strictly contracting map on all of `ℝᵈ`
(through `exists_lipschitz_graph_iff`). -/
theorem isEntireAcausalGraph_iff {S : Set (Minkowski d)} :
    IsEntireAcausalGraph S ↔ ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, IsStrictContraction g ∧
      S = graph g := by
  constructor
  · rintro ⟨hac, hmeet⟩
    have hach := minkowski_isAchronal_of_isAcausal hac
    obtain ⟨g, -, rfl⟩ := exists_lipschitz_graph_iff.2 fun p v hv =>
      existsUnique_of_exists_of_unique (hmeet p v hv) fun s s' hs hs' =>
        eq_of_mem_line_of_isAchronal hach p hv hs hs'
    exact ⟨g, isAcausal_graph_iff_isStrictContraction.1 hac, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨isAcausal_graph_iff_isStrictContraction.2 hg, fun p v hv =>
      (existsUnique_mem_graph_line hg.lipschitzWith p hv).exists⟩

private theorem minkB_add_smul_left (x y z : Minkowski d) (s : ℝ) :
    minkB (x + s • y) z = minkB x z + s * minkB y z := by
  simp only [minkB, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    inner_add_left, real_inner_smul_left]
  ring

/-- A null direction `ℓ ≠ 0`, or its opposite, is future causal. -/
private theorem exists_future_null {ℓ : Minkowski d} (hℓ0 : ℓ ≠ 0) (hℓ : minkQ ℓ = 0) :
    ∃ ℓ' : Minkowski d, IsFutureCausal ℓ' ∧ ℓ' ≠ 0 ∧ (ℓ' = ℓ ∨ ℓ' = -ℓ) := by
  have h1 : ℓ.1 ≠ 0 := fun h => hℓ0 (eq_zero_of_fst_eq_zero h hℓ.le)
  rcases lt_or_gt_of_ne h1 with h | h
  · exact ⟨-ℓ, ⟨by simp; linarith, by simpa using hℓ.le⟩, neg_ne_zero.2 hℓ0, Or.inr rfl⟩
  · exact ⟨ℓ, ⟨h.le, hℓ.le⟩, hℓ0, Or.inl rfl⟩

/-- Transfer along a Cauchy surface of `W`: a causal line meeting `S ⊆ W` meets `S'`. -/
private theorem line_meets_of_meets {W : Opens (Minkowski d)} {S S' : Set (Minkowski d)}
    (hSW : S ⊆ W) (hC' : (minkowski d).IsCauchySurfaceOn W S') {p v : Minkowski d}
    (hv : IsFutureCausal v) (hv0 : v ≠ 0) (h : ∃ s : ℝ, p + s • v ∈ S) :
    ∃ s : ℝ, p + s • v ∈ S' := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := exists_mem_line_of_isCauchySurfaceOn hC' (hSW hs) hv hv0
  exact ⟨s + s', by rwa [add_smul, ← add_assoc]⟩

/-- **(CC′) transfers between two Cauchy surfaces of one open set** (`docs/BARBOT-WAVE3.md`
§1C): if `S ⊆ W` satisfies (CC′) and is a Cauchy surface of `W`, every Cauchy surface `S' ⊆ W`
of `W` satisfies (CC′). Acausality of `S'` comes from the causal convexity of `W`
(`segment_subset_of_isCauchySurfaceOn`). -/
theorem ccPrime_of_isCauchySurfaceOn {W : Opens (Minkowski d)} {S S' : Set (Minkowski d)}
    (h : CCPrime S) (hSW : S ⊆ W) (hC : (minkowski d).IsCauchySurfaceOn W S)
    (hS'W : S' ⊆ W) (hC' : (minkowski d).IsCauchySurfaceOn W S') : CCPrime S' := by
  refine ⟨⟨?_, fun p v hv => line_meets_of_meets hSW hC' ⟨hv.1.le, hv.2.le⟩
    (fun h0 => by simp [h0] at hv; exact lt_irrefl _ hv.1) (h.entire.meets p v hv)⟩, ?_⟩
  · -- acausality of `S'`
    intro x hx y hy hxy
    by_contra hne
    obtain ⟨hseg, -⟩ := segment_subset_of_isCauchySurfaceOn h.entire.acausal hC (hS'W hx)
      (hS'W hy) hxy
    set v := y - x with hvdef
    have hv : IsFutureCausal v := le_top_iff_minkQ.1 hxy
    have hv0 : v ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hv1 := fst_pos_of_ne hv hv0
    have hyv : y.1 = x.1 + 1 * v.1 := by simp [hvdef]
    have hcy : timeLine x v y.1 = y := by rw [hyv, timeLine_param hv1, one_smul, hvdef]; abel
    have hxy1 : x.1 ≤ y.1 := by rw [hyv]; linarith
    have hJ : y.1 ∈ ordConnectedComponent (univ ∩ timeLine x v ⁻¹' W) x.1 := by
      rw [mem_ordConnectedComponent, uIcc_of_le hxy1]
      intro τ hτ
      refine ⟨trivial, hseg ?_⟩
      rw [segment_eq_image']
      refine ⟨(τ - x.1) / v.1, ⟨div_nonneg (by linarith [hτ.1]) hv1.le, (div_le_one hv1).2
        (by linarith [hτ.2])⟩, ?_⟩
      simp only [timeLine, hvdef]
    obtain ⟨_, -, huniq⟩ := hC' _ _ (Causality.inextensible_ordConnectedComponent
      minkowski_isCausal (inextensible_timeLine x hv hv0) (mem_univ x.1)
      (show timeLine x v x.1 ∈ W by rw [timeLine_self hv1]; exact hS'W hx))
    have e1 := huniq x ⟨⟨x.1, self_mem_ordConnectedComponent.2
      ⟨trivial, by rw [mem_preimage, timeLine_self hv1]; exact hS'W hx⟩, timeLine_self hv1⟩, hx⟩
    have e2 := huniq y ⟨⟨y.1, hJ, hcy⟩, hy⟩
    exact hne (e1.trans e2.symm)
  · -- null saturation of `S'`
    intro p ℓ hℓ0 hℓ ⟨q, hq, hqp⟩ r hr
    obtain ⟨ℓ', hℓ', hℓ'0, hℓ'e⟩ := exists_future_null hℓ0 hℓ
    have hBℓ : minkB ℓ' ℓ = 0 := by
      rcases hℓ'e with rfl | rfl
      · rw [← minkQ_eq_minkB]; exact hℓ
      · have := minkB_add_smul_left 0 ℓ ℓ (-1)
        simp only [zero_add, neg_one_smul, neg_one_mul] at this
        rw [this, ← minkQ_eq_minkB, hℓ]; simp [minkB]
    have hback : ∀ (x : Minkowski d) (A : Set (Minkowski d)), (∃ s : ℝ, x + s • ℓ' ∈ A) →
        ∃ s : ℝ, x + s • ℓ ∈ A := by
      rintro x A ⟨s, hs⟩
      rcases hℓ'e with rfl | rfl
      · exact ⟨s, hs⟩
      · exact ⟨-s, by rwa [neg_smul, ← smul_neg]⟩
    -- the hyperplane meets `S`
    obtain ⟨s₀, hs₀⟩ := exists_mem_line_of_isCauchySurfaceOn hC (hS'W hq) hℓ' hℓ'0
    have hP : ∃ q₀ ∈ S, minkB (q₀ - p) ℓ = 0 := ⟨_, hs₀, by
      rw [show q + s₀ • ℓ' - p = (q - p) + s₀ • ℓ' by abel, minkB_add_smul_left, hqp, hBℓ]
      ring⟩
    obtain ⟨s₁, hs₁⟩ := h.nullSat p ℓ hℓ0 hℓ hP r hr
    -- and so every `ℓ`-line of it meets `S'`
    have hrS : ∃ s : ℝ, r + s • ℓ' ∈ S := by
      rcases hℓ'e with rfl | rfl
      · exact ⟨s₁, hs₁⟩
      · exact ⟨-s₁, by rwa [neg_smul, smul_neg, neg_neg]⟩
    exact hback r S' (line_meets_of_meets hSW hC' hℓ' hℓ'0 hrS)

/-- **(CC′)(b) for the hyperboloid**: on a null hyperplane `ℓ^⊥ + p`, `⟨r | ℓ⟩` is constant, so
by `exists_mem_graph_hyperboloid_null_iff` either every `ℓ`-line of it meets the hyperboloid or
none does. -/
theorem nullSaturated_graph_hyperboloid : NullSaturated (graph (hyperboloid d)) := by
  intro p ℓ hℓ0 hℓ ⟨q, hq, hqp⟩ r hr
  have hsub : ∀ x : Minkowski d, minkB (x - p) ℓ = minkB x ℓ - minkB p ℓ := fun x => by
    simp only [minkB, Prod.fst_sub, Prod.snd_sub, inner_sub_left]; ring
  have h1 : ℓ.1 * minkB q ℓ < 0 :=
    (exists_mem_graph_hyperboloid_null_iff hℓ0 hℓ).1 ⟨0, by simpa using hq⟩
  refine (exists_mem_graph_hyperboloid_null_iff hℓ0 hℓ).2 ?_
  rw [hsub] at hqp hr
  have : minkB r ℓ = minkB q ℓ := by linarith
  rwa [this]

/-- **The hyperboloid satisfies (CC′)** although it is no Cauchy surface of `𝐌ⁿ` for `0 < d`
(`not_isCauchySurface_graph_hyperboloid`): (CC′) is Cauchy-completeness, not Cauchy-ness in
`𝐌ⁿ`. A non-vacuity witness for `CCPrime` (kb/0011). -/
theorem ccPrime_graph_hyperboloid : CCPrime (graph (hyperboloid d)) :=
  ⟨isEntireAcausalGraph_iff.2 ⟨_, fun _ _ h => abs_hyperboloid_sub_lt h, rfl⟩,
    nullSaturated_graph_hyperboloid⟩

/-- The horizontal hyperplanes `t = a` satisfy (CC′). -/
theorem ccPrime_graph_const (a : ℝ) : CCPrime (graph fun _ : EuclideanSpace ℝ (Fin d) => a) := by
  refine ⟨isEntireAcausalGraph_iff.2 ⟨_, fun x y h => ?_, rfl⟩, fun p ℓ hℓ0 hℓ _ r _ => ?_⟩
  · simpa using norm_pos_iff.2 (sub_ne_zero.2 h)
  · have ha : ℓ.1 ≠ 0 := fun h => hℓ0 (eq_zero_of_fst_eq_zero h hℓ.le)
    refine ⟨(a - r.1) / ℓ.1, ?_⟩
    rw [mem_graph]
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    ring

/-! ### D. The domain of dependence -/

/-- **The domain of dependence** `D(S)` of `S` in the open `W`, for a general causality: the
points `p ∈ W` such that every inextensible causal curve of `W` through `p` meets `S`. -/
def dependenceDomain {M : Type*} [TopologicalSpace M] (C : Causality M) (W : Opens M)
    (S : Set M) : Set M :=
  {p | p ∈ W ∧ ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → p ∈ c '' I →
    (c '' I ∩ S).Nonempty}

section dependence

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {W : Opens M} {S : Set M}

theorem mem_dependenceDomain {p : M} : p ∈ dependenceDomain C W S ↔ p ∈ W ∧
    ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → p ∈ c '' I → (c '' I ∩ S).Nonempty :=
  Iff.rfl

theorem dependenceDomain_subset : dependenceDomain C W S ⊆ W := fun _ hp => hp.1

theorem subset_dependenceDomain (hSW : S ⊆ W) : S ⊆ dependenceDomain C W S :=
  fun p hp => ⟨hSW hp, fun _ _ _ hpc => ⟨p, hpc, hp⟩⟩

/-- A Cauchy surface of `W` has all of `W` for domain of dependence. -/
theorem dependenceDomain_eq_of_isCauchySurfaceOn (h : C.IsCauchySurfaceOn W S) :
    dependenceDomain C W S = W :=
  Subset.antisymm dependenceDomain_subset fun _ hp => ⟨hp, fun I c hc _ => by
    obtain ⟨x, hx, -⟩ := h I c hc
    exact ⟨x, hx⟩⟩

end dependence

/-- Under the null-line criterion, the domain of dependence of a strictly contracting graph is
all of `𝐌ⁿ`. -/
theorem dependenceDomain_graph_eq_univ (hf : IsStrictContraction f)
    (hnull : ∀ p v : Minkowski d, v ≠ 0 → minkQ v = 0 → ∃ s : ℝ, p + s • v ∈ graph f) :
    dependenceDomain (minkowski d) ⊤ (graph f) = univ := by
  rw [dependenceDomain_eq_of_isCauchySurfaceOn ((isCauchySurface_graph_iff hf).2 hnull)]
  rfl

/-- The cylinder step, past side: near a point `p` of a strictly contracting graph, a past causal
curve (time `→ −∞`) starting with `T < ε` reaches `T ≤ 0`: either it stays in the unit cylinder
around `p`, where `f` is bounded, or it crosses its wall, where `f ≥ f(p.2) − c₀`, `c₀ < 1`. -/
private theorem cylinder_past (hf : IsStrictContraction f) {p : Minkowski d} (hp : p ∈ graph f) :
    ∃ ε > 0, ∀ g : ℝ → Minkowski d, Continuous g →
      (∀ s s', s ≤ s' → ‖(g s').2 - (g s).2‖ ≤ (g s').1 - (g s).1) →
      Tendsto (fun s => (g s).1) atBot atBot → ∀ t₀, ‖(g t₀).2 - p.2‖ < ε →
        timeSub f (g t₀) < ε → ∃ s ≤ t₀, timeSub f (g s) ≤ 0 := by
  have hlip := hf.lipschitzWith
  have hL : ∀ x y, |f x - f y| ≤ ‖x - y‖ := abs_sub_le_norm_of_lipschitzWith_one hlip
  -- the constant `c₀ < 1` on the unit sphere around `p.2`
  obtain ⟨c₀, hc₀, hc₀1, hsph⟩ : ∃ c₀ : ℝ, 0 ≤ c₀ ∧ c₀ < 1 ∧
      ∀ x ∈ sphere p.2 1, |f x - f p.2| ≤ c₀ := by
    rcases (sphere p.2 (1 : ℝ)).eq_empty_or_nonempty with h | h
    · exact ⟨0, le_rfl, one_pos, fun x hx => by rw [h] at hx; exact absurd hx (notMem_empty x)⟩
    · obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_sphere p.2 1).exists_isMaxOn h
        ((continuous_abs.comp (hlip.continuous.sub continuous_const)).continuousOn)
      have hx₀n : ‖x₀ - p.2‖ = 1 := by rw [← dist_eq_norm]; exact hx₀
      refine ⟨|f x₀ - f p.2|, abs_nonneg _, ?_, fun x hx => hmax hx⟩
      rw [← hx₀n]
      exact hf x₀ p.2 fun h => by rw [h, sub_self, norm_zero] at hx₀n; exact zero_ne_one hx₀n
  have hp0 : p.1 = f p.2 := hp
  refine ⟨(1 - c₀) / 4, by linarith, fun g hg hmono ht t₀ hy hTy => ?_⟩
  by_cases hA : ∀ s ≤ t₀, ‖(g s).2 - p.2‖ < 1
  · obtain ⟨s, hs1, hs2⟩ := ((ht.eventually (eventually_lt_atBot (f p.2 - 1))).and
      (eventually_le_atBot t₀)).exists
    refine ⟨s, hs2, ?_⟩
    have h1 := hA s hs2
    have h2 := hL p.2 (g s).2
    rw [norm_sub_rev] at h2
    simp only [timeSub]
    linarith [le_abs_self (f p.2 - f (g s).2)]
  · push Not at hA
    obtain ⟨s₁, hs₁, hs₁'⟩ := hA
    have hcont : ContinuousOn (fun s => ‖(g s).2 - p.2‖) (Icc s₁ t₀) :=
      ((continuous_snd.comp hg).sub continuous_const).norm.continuousOn
    obtain ⟨s, hs, hs1⟩ := intermediate_value_Icc' hs₁ hcont
      (show (1 : ℝ) ∈ Icc ‖(g t₀).2 - p.2‖ ‖(g s₁).2 - p.2‖ from ⟨by linarith, hs₁'⟩)
    refine ⟨s, hs.2, ?_⟩
    have hsph' : (g s).2 ∈ sphere p.2 1 := by rw [mem_sphere, dist_eq_norm]; exact hs1
    have h1 := hsph _ hsph'
    have h2 := hmono s t₀ hs.2
    have hs1' : ‖(g s).2 - p.2‖ = 1 := hs1
    have h3 : ‖(g s).2 - p.2‖ ≤ ‖(g t₀).2 - (g s).2‖ + ‖(g t₀).2 - p.2‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (g s).2 (g t₀).2 p.2
      rwa [norm_sub_rev (g s).2 (g t₀).2] at this
    have h4 := hL (g t₀).2 p.2
    simp only [timeSub] at hTy ⊢
    linarith [le_abs_self (f (g t₀).2 - f p.2), neg_abs_le (f (g s).2 - f p.2)]

/-- **A strictly contracting entire graph lies in the interior of its domain of dependence**
(`docs/BARBOT-WAVE3.md` §1D): a neighbourhood `{‖x − p.2‖ < ε, |T| < ε}` of each of its points
is in `D(S)`, by the cylinder step on both sides and the intermediate value theorem. -/
theorem graph_subset_interior_dependenceDomain (hf : IsStrictContraction f) :
    graph f ⊆ interior (dependenceDomain (minkowski d) ⊤ (graph f)) := by
  intro p hp
  have hlip := hf.lipschitzWith
  obtain ⟨ε₁, hε₁, h₁⟩ := cylinder_past hf hp
  have hp' : refl p ∈ graph fun x => -f x := by
    simp only [mem_graph, refl]; rw [mem_graph] at hp; rw [hp]
  obtain ⟨ε₂, hε₂, h₂⟩ := cylinder_past hf.neg hp'
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  set U : Set (Minkowski d) := {y | ‖y.2 - p.2‖ < ε ∧ |timeSub f y| < ε} with hU
  have hUo : IsOpen U :=
    (isOpen_lt ((continuous_snd.sub continuous_const).norm) continuous_const).inter
      (isOpen_lt (continuous_timeSub hlip).abs continuous_const)
  have hpU : p ∈ U := show _ ∧ _ from
    ⟨by simpa using hε, by rw [mem_graph_iff_timeSub.1 hp, abs_zero]; exact hε⟩
  refine interior_maximal (fun y hy => (mem_dependenceDomain (C := minkowski d) (W := ⊤)
    (S := graph f)).2 ⟨trivial, fun I c hc hyc => ?_⟩) hUo hpU
  refine exists_mem_graph_of_reparam hlip hc fun g hg hr => ?_
  obtain ⟨t₀, rfl⟩ : y ∈ range g := hr ▸ hyc
  have hmono : ∀ s s', s ≤ s' → ‖(g s').2 - (g s).2‖ ≤ (g s').1 - (g s).1 := fun s s' h =>
    minkowski_le_top_iff.1 (hg.1.le_of_le trivial trivial h)
  have hTy := (abs_lt.1 hy.2)
  obtain ⟨s₁, -, hs₁⟩ := h₁ g hg.1.continuous hmono (staticCausality.tendsto_time_atBot hg) t₀
    (hy.1.trans_le (min_le_left _ _)) (hTy.2.trans_le (min_le_left _ _))
  -- the future side, by time reflection
  set g' : ℝ → Minkowski d := fun s => refl (g (-s)) with hg'
  have hg'c : Continuous g' :=
    (continuous_fst.neg.prodMk continuous_snd).comp (hg.1.continuous.comp continuous_neg)
  have hmono' : ∀ s s', s ≤ s' → ‖(g' s').2 - (g' s).2‖ ≤ (g' s').1 - (g' s).1 := by
    intro s s' h
    have := hmono (-s') (-s) (neg_le_neg h)
    simp only [hg', refl]
    rw [norm_sub_rev]; linarith
  have ht' : Tendsto (fun s => (g' s).1) atBot atBot := by
    simp only [hg', refl]
    exact tendsto_neg_atTop_atBot.comp
      ((staticCausality.tendsto_time_atTop hg).comp tendsto_neg_atBot_atTop)
  obtain ⟨s₂, -, hs₂⟩ := h₂ g' hg'c hmono' ht' (-t₀)
    (by simpa [hg', refl] using hy.1.trans_le (min_le_right _ _))
    (by
      simp only [hg', neg_neg]
      rw [timeSub_neg_refl]
      linarith [hTy.1, min_le_right ε₁ ε₂])
  refine ⟨⟨s₁, hs₁⟩, ⟨-s₂, ?_⟩⟩
  have := hs₂
  simp only [hg'] at this
  rw [timeSub_neg_refl] at this
  linarith

/-- **`S` is a Cauchy surface of the interior of its domain of dependence**, for a strictly
contracting entire graph (`docs/BARBOT-WAVE3.md` §1D). Uniqueness is proved; existence is not. -/
theorem isCauchySurfaceOn_interior_dependenceDomain (hf : IsStrictContraction f) :
    (minkowski d).IsCauchySurfaceOn
      ⟨interior (dependenceDomain (minkowski d) ⊤ (graph f)), isOpen_interior⟩ (graph f) := by
  intro I c hc
  have huniq : ∀ x y, x ∈ c '' I ∩ graph f → y ∈ c '' I ∩ graph f → x = y := fun x y hx hy =>
    unique_of_isAcausal (isAcausal_graph_iff_isStrictContraction.2 hf)
      (hc.1.mono_opens le_top) hx hy
  have hex : (c '' I ∩ graph f).Nonempty := by
    sorry -- SORRY(D-cauchy-interior): a causal curve inextensible in `W = int D(S)` (not in `𝐌ⁿ`) with `T > 0` throughout has its past part in the compact `J⁻(c t₀) ∩ {T ≥ 0}` (`bddBelow_fst_Jminus_inter`, valid as every causal line through `c t₀ ∈ D(S)` meets `S`), so time converges and the curve has a past limit `P`; one needs (1) `P ∈ W`, i.e. `J⁻(y) ∩ {T ≥ 0} ⊆ int D(S)` for `y ∈ int D(S)` (concatenating inextensible curves through `y`, and openness), and (2) a `W`-relative `pastExtensible_of_tendsto` (the library has it for `⊤` only, `Causal/Inextensible.lean:859`, and `Inextensible.reparam` for `⊤` only, `Causal/Cauchy.lean:251`)
  obtain ⟨x, hx⟩ := hex
  exact ⟨x, hx, fun y hy => huniq y x hy hx⟩

/-- A unit vector `e` with `⟪x, e⟫ = ‖x‖`, for `0 < d`. -/
private theorem exists_unit_inner_eq_norm (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 ∧ inner ℝ x e = ‖x‖ := by
  by_cases hx : x = 0
  · exact ⟨unitVec d hd, norm_unitVec hd, by simp [hx]⟩
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp

/-- **Rem 2.2, the standard example: the domain of dependence of the hyperboloid is the open
future cone** `{Q < 0, t > 0}` (`0 < d`). A point outside it lies on a null line missing the
cone; a point inside it sees `T → −∞` in the past (`t ≤ 0` eventually) and `T ≥ 0` in the
future (`J⁺(p)` is eventually above the hyperboloid). -/
theorem dependenceDomain_hyperboloid (hd : 0 < d) :
    dependenceDomain (minkowski d) ⊤ (graph (hyperboloid d)) = {p | IsFutureTimelike p} := by
  ext p
  constructor
  · intro hp
    obtain ⟨-, hp⟩ := mem_dependenceDomain.1 hp
    by_contra hpc
    rw [mem_setOf_eq, isFutureTimelike_iff_norm_lt, not_lt] at hpc
    obtain ⟨e, he, hin⟩ := exists_unit_inner_eq_norm hd p.2
    set ℓ : ℝ → EuclideanSpace ℝ (Fin d) := fun τ => p.2 + (τ - p.1) • e with hℓ
    have hℓd : ∀ s s', dist (ℓ s) (ℓ s') = |s - s'| := fun s s' => by
      rw [dist_eq_norm]; simp only [hℓ, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, he,
        Real.norm_eq_abs, mul_one]; ring_nf
    have hc := staticCausality.inextensible_nullLine hℓd
    obtain ⟨_, ⟨τ, -, rfl⟩, hτ⟩ := hp univ _ hc ⟨p.1, trivial, by simp [hℓ]⟩
    rw [mem_graph] at hτ
    simp only at hτ
    have h1 : τ ≤ ‖ℓ τ‖ := by
      have := real_inner_le_norm (ℓ τ) e
      rw [he, mul_one] at this
      have h2 : inner ℝ (ℓ τ) e = ‖p.2‖ + (τ - p.1) := by
        simp only [hℓ, inner_add_left, real_inner_smul_left, hin, real_inner_self_eq_norm_sq, he]
        ring
      linarith
    have h3 : ‖ℓ τ‖ < hyperboloid d (ℓ τ) :=
      (Real.lt_sqrt (norm_nonneg _)).2 (by linarith)
    linarith
  · intro hp
    refine mem_dependenceDomain.2 ⟨trivial, fun I c hc hpc =>
      exists_mem_graph_of_reparam lipschitzWith_one_hyperboloid hc fun g hg hr => ?_⟩
    obtain ⟨t₀, ht₀⟩ : p ∈ range g := hr ▸ hpc
    refine ⟨?_, ?_⟩
    · obtain ⟨s, hs⟩ := ((staticCausality.tendsto_time_atBot hg).eventually
        (eventually_le_atBot 0)).exists
      exact ⟨s, by simp only [timeSub]; linarith [hyperboloid_pos (d := d) (g s).2]⟩
    · have ha := sub_pos.2 (norm_snd_lt_fst hp)
      set a := p.1 - ‖p.2‖
      set B := max a ((1 + a ^ 2) / (2 * a))
      obtain ⟨s, hs1, hs2⟩ := (((staticCausality.tendsto_time_atTop hg).eventually
        (eventually_ge_atTop B)).and (eventually_ge_atTop t₀)).exists
      refine ⟨s, ?_⟩
      have hle := minkowski_le_top_iff.1 (hg.1.le_of_le trivial trivial hs2)
      rw [ht₀] at hle
      have hx : ‖(g s).2‖ ≤ (g s).1 - a := by
        have := norm_sub_norm_le (g s).2 p.2
        simp only [a]; linarith
      have htB1 : a ≤ (g s).1 := (le_max_left _ _).trans hs1
      have htB2 : (1 + a ^ 2) / (2 * a) ≤ (g s).1 := (le_max_right _ _).trans hs1
      rw [div_le_iff₀ (by linarith)] at htB2
      have hsq : 1 + ‖(g s).2‖ ^ 2 ≤ (g s).1 ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hx 2
        nlinarith
      simp only [timeSub, hyperboloid]
      have := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq (by linarith)] at this
      linarith

theorem isOpen_setOf_isFutureTimelike : IsOpen {p : Minkowski d | IsFutureTimelike p} := by
  have : {p : Minkowski d | IsFutureTimelike p} = {p | ‖p.2‖ < p.1} := by
    ext p; exact isFutureTimelike_iff_norm_lt
  rw [this]
  exact isOpen_lt (continuous_norm.comp continuous_snd) continuous_fst

/-- `D(hyperboloid)` is open. -/
theorem isOpen_dependenceDomain_hyperboloid (hd : 0 < d) :
    IsOpen (dependenceDomain (minkowski d) ⊤ (graph (hyperboloid d))) := by
  rw [dependenceDomain_hyperboloid hd]
  exact isOpen_setOf_isFutureTimelike

/-- **Rem 2.2, first half** (l.542): the hyperboloid is a Cauchy surface of the open future cone
`Ω`, as `int D(S) = D(S) = Ω`. Rests on `isCauchySurfaceOn_interior_dependenceDomain`. -/
theorem isCauchySurfaceOn_futureCone_hyperboloid (hd : 0 < d) :
    (minkowski d).IsCauchySurfaceOn ⟨{p | IsFutureTimelike p}, isOpen_setOf_isFutureTimelike⟩
      (graph (hyperboloid d)) := by
  have h := isCauchySurfaceOn_interior_dependenceDomain (d := d)
    (fun _ _ h => abs_hyperboloid_sub_lt h)
  have hW : (⟨interior (dependenceDomain (minkowski d) ⊤ (graph (hyperboloid d))),
      isOpen_interior⟩ : Opens (Minkowski d)) =
        ⟨{p | IsFutureTimelike p}, isOpen_setOf_isFutureTimelike⟩ :=
    Opens.ext (show interior _ = _ by
      rw [(isOpen_dependenceDomain_hyperboloid hd).interior_eq, dependenceDomain_hyperboloid hd]
      rfl)
  rw [hW] at h
  exact h

/-- **The null lines the hyperboloid meets are those entering the open future cone**
`Ω = {t > ‖x‖} = D(S)`: `⇒` as `S ⊆ Ω`; `⇐` as a point of the line in `Ω` is in `D(S)`
(`dependenceDomain_hyperboloid`) and the line is inextensible. (No `0 < d` is assumed: a nonzero
null vector forces it.) -/
theorem exists_mem_graph_hyperboloid_null_iff_isFutureTimelike {r ℓ : Minkowski d} (hℓ0 : ℓ ≠ 0)
    (hℓ : minkQ ℓ = 0) :
    (∃ s : ℝ, r + s • ℓ ∈ graph (hyperboloid d)) ↔ ∃ s : ℝ, IsFutureTimelike (r + s • ℓ) := by
  constructor
  · rintro ⟨s, hs⟩
    rw [graph_hyperboloid] at hs
    exact ⟨s, hs.2, by linarith [hs.1]⟩
  · rintro ⟨s, hs⟩
    have hd : 0 < d := Nat.pos_of_ne_zero fun h => by
      subst h
      have h2 : ℓ.2 = 0 := Subsingleton.elim _ _
      have h1 : ℓ.1 = 0 := by
        have := hℓ
        simp only [minkQ, h2, norm_zero] at this
        nlinarith [sq_nonneg ℓ.1]
      exact hℓ0 (eq_zero_of_fst_eq_zero h1 hℓ.le)
    set P := r + s • ℓ with hP
    have hPD : P ∈ dependenceDomain (minkowski d) ⊤ (graph (hyperboloid d)) := by
      rw [dependenceDomain_hyperboloid hd]; exact hs
    obtain ⟨ℓ', hℓ', hℓ'0, hℓ'e⟩ := exists_future_null hℓ0 hℓ
    have hv1 := fst_pos_of_ne hℓ' hℓ'0
    obtain ⟨_, ⟨τ, -, rfl⟩, hx⟩ := (mem_dependenceDomain.1 hPD).2 univ (timeLine P ℓ')
      (inextensible_timeLine P hℓ' hℓ'0) ⟨P.1, trivial, timeLine_self hv1⟩
    rw [timeLine_eq_add_smul, hP] at hx
    rcases hℓ'e with rfl | rfl
    · exact ⟨s + (τ - (r + s • ℓ').1) / ℓ'.1, by rwa [add_smul, ← add_assoc]⟩
    · refine ⟨s - (τ - (r + s • ℓ).1) / (-ℓ).1, ?_⟩
      rwa [sub_smul, sub_eq_add_neg, ← add_assoc, ← smul_neg] at *

end Causal.Flat
