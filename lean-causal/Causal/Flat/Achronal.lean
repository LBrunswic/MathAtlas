import Causal.Flat.Form
import Causal.CauchyExtension
import Causal.Geroch

/-!
# `Causal.Flat.Achronal` — achronal sets, entire spacelike graphs, and Cauchy graphs of `𝐌ⁿ`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257). No
b-label is certified: every statement used here is prose. The causal core of three passages:

* **[8.G]** (`GHFspace.tex` l.2307–2328), the developed Cauchy surface `S̃` after `bcor:quo`:

  > As an immediate corollary of proposition \ref{project}, we obtain that
  > $\widetilde{S}$ is the graph of a contracting map
  > $\varphi: {\mathbb R}^{n-1} \rightarrow {\mathbb R}$. […]
  > Another corollary is the following global property: spacelike hypersurfaces
  > are achronal closed set, meaning that if $x$ and $y$ are two distinct points in
  > $\widetilde{S}$, one cannot be contained in the past of future cone of the other, i.e., we
  > have $\mid x-y \mid^{2}>0$. (l.2307–2326)

  and `bcor:quo` (l.2263–2270): "${\mathcal D} \circ \tilde{f}(\widetilde{S})$ intersects every
  timelike geodesic."
* **Rem 2.2** (l.538–546):

  > in \mink, let $\Omega$ be a connected component of the negative cone $\{ Q< 0 \}$.
  > Then, $S = \Omega \cap \{ Q=-1 \}$ is a Cauchy hypersurface for $\Omega$. […]
  > The point is that $S$ is not a Cauchy hypersurface in \mink, therefore,
  > the inclusion $\Omega \subset {\bf M}^{n}$ is not a Cauchy embedding. (l.540–545)
* **[3.U]**'s Cauchy argument (l.729–741), which checks causal geodesics only:

  > Now, a nonspacelike geodesic in $\Omega$ is the intersection between $\Omega$ and a
  > nonspacelike geodesic line $d$ of \mink. […]
  > Hence, any nonspacelike geodesic intersect $S_{f}$: this is a criteria proving that
  > $S_{f}$ is indeed a Cauchy hypersurface. (l.731–741)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; the library's `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's `n` is `d + 1` and his
`ℝ^{n−1}` is `EuclideanSpace ℝ (Fin d)`.

## What is proved

* `Causality.IsAchronal` — no two points of `S` chronologically related in `M`, for a general
  causality (beside the library's `IsAcausal`); `dual_isAchronal`, `IsAchronal.mono`,
  `IsAcausal.isAchronal` (under chronology), `IsAcausal.isAchronal_of_causallyArcConnected`
  (instantiated on `minkowski d` by `minkowski_isAchronal_of_isAcausal`).
* In `𝐌ⁿ`: `isAchronal_iff_minkQ` (`0 ≤ |x − y|²`), `isAcausal_iff_minkQ` (Barbot's
  `|x − y|² > 0` for distinct points, l.2326, is **acausality**).
* `graph f = {(t, x) | t = f x}`; `isAchronal_graph_iff` (↔ `LipschitzWith 1 f`),
  `isAcausal_graph_iff` (↔ `|f x − f y| < ‖x − y‖` for `x ≠ y`, one reading of Barbot's
  "contracting"),
  `isClosed_graph`.
* `exists_lipschitz_graph_of_isAchronal` — an achronal set meeting every vertical line once is
  the graph of a 1-Lipschitz map (`exists_lipschitz_graph_of_isAchronal_of_exists`: "at least
  once" suffices, uniqueness being automatic); `eq_of_mem_line_of_isAchronal` — an achronal set meets a
  timelike line at most once; `existsUnique_mem_graph_line` — an entire 1-Lipschitz graph meets
  every timelike affine line `{p + s • v}` exactly once; `exists_lipschitz_graph_iff` — the
  two together: **`S` is an entire 1-Lipschitz graph iff it meets every timelike line exactly
  once** ((CC′)(a) of `docs/BARBOT.md`).
* **The Cauchy criterion** `isCauchySurface_graph`: if `f` is `κ`-Lipschitz with `κ < 1`, then
  `graph f` is a Cauchy surface of `minkowski d` in the ETT sense (DEC-14: every inextensible
  causal curve over any interval meets it exactly once), through `t − f(x)` being a Cauchy time
  function strictly increasing along `≤` (`isCauchyTimeFunction_graphTime`,
  `graphTime_lt_of_le`) and `IsCauchyTimeFunction.isCauchySurface` (`Causal/Geroch.lean`).
* **The counterexample of Rem 2.2** (DEC-27 style): the hyperboloid `t = √(1 + ‖x‖²)` is
  `Ω ∩ {Q = −1}` (`graph_hyperboloid`), closed, entire and acausal, and for `0 < d` it is **not**
  a Cauchy surface of `minkowski d` (`not_isCauchySurface_graph_hyperboloid`): the inextensible
  null line `τ ↦ (τ, τe)` misses it. Hence no `κ < 1` makes it `κ`-Lipschitz
  (`not_lipschitz_hyperboloid`), and "entire acausal graph" does not imply Cauchy
  (`not_forall_isAcausal_graph_isCauchySurface`). For `d = 0` the hyperboloid is a point and is
  a Cauchy surface (`isCauchySurface_graph_hyperboloid_zero`).
* **Rem 2.2 for either component `Ω`.** The connected components of `{Q < 0}` are exactly the
  open future and past timelike cones (`connectedComponentIn_of_fst_pos`,
  `connectedComponentIn_of_fst_neg`), the lower sheet is the graph of `−√(1 + ‖x‖²)`
  (`graph_neg_hyperboloid`), and for `0 < d` and every component `Ω`, `Ω ∩ {Q = −1}` is not a
  Cauchy surface of `𝐌ⁿ` (`not_isCauchySurface_connectedComponentIn_inter`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| [8.G] `S̃` is the developed complete spacelike hypersurface | ⚠ replaced: an arbitrary entire graph `graph f` (that `S̃` is one is `bprop:project`, not carried) |
| [8.G] "contracting" | ✓ carried in two readings: 1-Lipschitz (↔ achronal), strictly contracting (↔ acausal) |
| [8.G] "closed" | ✓ carried for continuous `f` |
| `bcor:quo` `S̃` developed by `𝒟 ∘ f̃` | ⚠ replaced: an entire 1-Lipschitz graph; only "intersects every timelike geodesic" is proved, exactly once |
| [3.U] `S_f ⊂ Ω`, checked on causal geodesics | not treated: [3.U]'s `S_f`, `Ω` and `IsCauchySurfaceOn Ω` are not stated; `isCauchySurface_graph` is a criterion for entire `κ`-Lipschitz graphs of `𝐌ⁿ`, `κ < 1`, over every inextensible causal curve (DEC-14) |
| Rem 2.2 `Ω` a connected component of `{Q < 0}` | ✓ carried: both components |
| Rem 2.2 `𝐌ⁿ`, any `n` | ⚠ strengthened: `0 < d` (`n ≥ 2`); false for `d = 0`, see `isCauchySurface_graph_hyperboloid_zero` |

## SCOPE (disclosed)

* No b-label: the passages are prose. Line numbers are those of the labelled
  `papers/barbot/legacy/labeled/GHFspace.tex`; `docs/BARBOT.md` cites Rem 2.2 at l.536 and [8.G]
  at l.2278, two lines and ~30 lines earlier than in this copy.
* "Contracting" (l.2308) is read two ways and both are proved: weakly (1-Lipschitz, achronal)
  and strictly (`|f x − f y| < ‖x − y‖`, acausal, Barbot's `|x − y|² > 0`). Neither is enough
  for Cauchy: the hyperboloid is strictly contracting. The criterion asks a uniform `κ < 1`.
* [3.U] proper is not attempted: nothing is stated about `S_f` or `Ω`; the file supplies only the
  `𝐌ⁿ` criterion that would close [3.U]'s method gap (existence on geodesics only, l.740).
* Rem 2.2's other half — `S` **is** a Cauchy hypersurface of `Ω` — is not attempted: it needs
  the curves inextensible in the open set `Ω` (`IsCauchySurfaceOn Ω`), not in `𝐌ⁿ`.
* The Cauchy criterion is stated for `M` (`U = ⊤`), as `IsCauchySurface` is used by the
  library's Geroch theorem; achronality and acausality are defined for `M` only, as `IsAcausal`.
* The norm on `Minkowski d` is the product (sup) norm (`Form.lean` SCOPE); only `p.2`'s Euclidean
  norm enters a statement.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 1, package WP-30b-Achronal.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

/-! ### Achronal sets of a general causality -/

namespace Causality

variable {M : Type*} [TopologicalSpace M] (C : Causality M)

/-- A set no two points of which are chronologically related in `M` (`x ≪ y` with `x, y ∈ S`
never holds, `x = y` included). -/
def IsAchronal (S : Set M) : Prop := ∀ x ∈ S, ∀ y ∈ S, ¬ C.lt ⊤ x y

variable {C} {S T : Set M}

theorem dual_isAchronal : C.dual.IsAchronal S ↔ C.IsAchronal S :=
  ⟨fun h x hx y hy hxy => h y hy x hx hxy, fun h x hx y hy hxy => h y hy x hx hxy⟩

theorem IsAchronal.mono (h : C.IsAchronal T) (hST : S ⊆ T) : C.IsAchronal S :=
  fun x hx y hy => h x (hST hx) y (hST hy)

/-- An acausal set is achronal in a chronological spacetime. -/
theorem IsAcausal.isAchronal (hchr : ∀ x, ¬ C.lt ⊤ x x) (h : C.IsAcausal S) : C.IsAchronal S := by
  intro x hx y hy hxy
  obtain rfl := h x hx y hy (C.le_of_lt hxy)
  exact hchr x hxy

/-- An acausal set is achronal in a causally arc-connected causal `T1` spacetime with
`J⁻(p) ≠ {p}` (chronology from `ne_of_lt_top`). -/
theorem IsAcausal.isAchronal_of_causallyArcConnected [T1Space M] (hC : C.CausallyArcConnected)
    (hcaus : C.IsCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (h : C.IsAcausal S) :
    C.IsAchronal S :=
  h.isAchronal fun _ hx => ne_of_lt_top hC hcaus hJm hx rfl

end Causality

namespace Flat

variable {d : ℕ}

/-! ### Achronal and acausal sets of `𝐌ⁿ` through the form -/

theorem minkowski_not_lt_self (p : Minkowski d) : ¬ (minkowski d).lt ⊤ p p := by
  rw [minkowski_lt_top_iff]; simp

/-- **Witness** (kb/0011, kb/0012): `minkowski d` satisfies the four hypotheses of
`IsAcausal.isAchronal_of_causallyArcConnected`. -/
theorem minkowski_isAchronal_of_isAcausal {S : Set (Minkowski d)}
    (h : (minkowski d).IsAcausal S) : (minkowski d).IsAchronal S :=
  h.isAchronal_of_causallyArcConnected minkowski_causallyArcConnected minkowski_isCausal
    staticCausality.Jminus_ne_singleton

/-- **Achronal in `𝐌ⁿ` iff `|x − y|² ≥ 0`** for all `x, y ∈ S`. -/
theorem isAchronal_iff_minkQ {S : Set (Minkowski d)} :
    (minkowski d).IsAchronal S ↔ ∀ p ∈ S, ∀ q ∈ S, 0 ≤ minkQ (q - p) := by
  constructor
  · intro h p hp q hq
    by_contra hneg
    rcases isFutureTimelike_or_neg (not_le.1 hneg) with h1 | h1
    · exact h p hp q hq (lt_top_iff_minkQ.2 h1)
    · exact h q hq p hp (lt_top_iff_minkQ.2 (by simpa using h1))
  · intro h p hp q hq hpq
    exact absurd (h p hp q hq) (not_le.2 (lt_top_iff_minkQ.1 hpq).2)

/-- **Acausal in `𝐌ⁿ` iff `|x − y|² > 0`** for distinct `x, y ∈ S`: Barbot's l.2326. -/
theorem isAcausal_iff_minkQ {S : Set (Minkowski d)} :
    (minkowski d).IsAcausal S ↔ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 0 < minkQ (q - p) := by
  constructor
  · intro h p hp q hq hne
    by_contra hneg
    have hle : minkQ (q - p) ≤ 0 := not_lt.1 hneg
    by_cases h0 : 0 ≤ (q - p).1
    · exact hne (h p hp q hq (le_top_iff_minkQ.2 ⟨h0, hle⟩))
    · have h1 : IsFutureCausal (p - q) := by
        refine ⟨?_, ?_⟩
        · have : (p - q).1 = -(q - p).1 := by simp
          rw [this]; linarith [not_le.1 h0]
        · rw [show p - q = -(q - p) by abel, minkQ_neg]; exact hle
      exact hne (h q hq p hp (le_top_iff_minkQ.2 h1)).symm
  · intro h p hp q hq hpq
    by_contra hne
    exact absurd (h p hp q hq hne) (not_lt.2 (le_top_iff_minkQ.1 hpq).2)

/-! ### Graphs over space -/

/-- The graph `{(t, x) | t = f x}` of `f : ℝᵈ → ℝ`, an entire hypersurface of `𝐌ⁿ`. -/
def graph (f : EuclideanSpace ℝ (Fin d) → ℝ) : Set (Minkowski d) := {p | p.1 = f p.2}

variable {f : EuclideanSpace ℝ (Fin d) → ℝ}

@[simp] theorem mem_graph {p : Minkowski d} : p ∈ graph f ↔ p.1 = f p.2 := Iff.rfl

theorem mk_mem_graph (x : EuclideanSpace ℝ (Fin d)) : ((f x, x) : Minkowski d) ∈ graph f := rfl

theorem isClosed_graph (hf : Continuous f) : IsClosed (graph f) :=
  isClosed_eq continuous_fst (hf.comp continuous_snd)

theorem abs_sub_le_of_lipschitz {κ : NNReal} (hf : LipschitzWith κ f)
    (x y : EuclideanSpace ℝ (Fin d)) : |f x - f y| ≤ κ * ‖x - y‖ := by
  have := hf.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm] at this

/-- **[8.G] An entire graph is achronal iff `f` is 1-Lipschitz.** -/
theorem isAchronal_graph_iff : (minkowski d).IsAchronal (graph f) ↔ LipschitzWith 1 f := by
  constructor
  · intro h
    refine LipschitzWith.of_le_add fun x y => ?_
    have := h (f y, y) rfl (f x, x) rfl
    rw [minkowski_lt_top_iff] at this
    rw [dist_eq_norm]
    linarith [not_lt.1 this]
  · intro hf p hp q hq hpq
    rw [minkowski_lt_top_iff] at hpq
    rw [mem_graph] at hp hq
    have := abs_sub_le_of_lipschitz hf q.2 p.2
    rw [hp, hq] at hpq
    simp only [NNReal.coe_one, one_mul] at this
    linarith [le_abs_self (f q.2 - f p.2)]

/-- **[8.G] An entire graph is acausal iff `f` is strictly contracting**: `|f x − f y| < ‖x − y‖`
for `x ≠ y`. -/
theorem isAcausal_graph_iff :
    (minkowski d).IsAcausal (graph f) ↔ ∀ x y, x ≠ y → |f x - f y| < ‖x - y‖ := by
  constructor
  · intro h x y hxy
    by_contra hle
    rcases le_abs.1 (not_lt.1 hle) with h1 | h1
    · have := h (f y, y) rfl (f x, x) (rfl) (minkowski_le_top_iff.2 (by simpa using h1))
      exact hxy (Prod.ext_iff.1 this).2.symm
    · have := h (f x, x) rfl (f y, y) (rfl) (minkowski_le_top_iff.2 (by
        rw [norm_sub_rev]; simpa using h1))
      exact hxy (Prod.ext_iff.1 this).2
  · intro h p hp q hq hpq
    by_contra hne
    rw [mem_graph] at hp hq
    have h2 : p.2 ≠ q.2 := fun h2 => hne (Prod.ext (by rw [hp, hq, h2]) h2)
    have h3 := h q.2 p.2 (Ne.symm h2)
    have h4 := minkowski_le_top_iff.1 hpq
    rw [hp, hq] at h4
    linarith [le_abs_self (f q.2 - f p.2)]

/-! ### Graphs and timelike lines -/

/-- Two points of a timelike affine line are chronologically related. -/
theorem lt_top_line (p : Minkowski d) {v : Minkowski d} (hv : IsFutureTimelike v) {s s' : ℝ}
    (hss' : s < s') : (minkowski d).lt ⊤ (p + s • v) (p + s' • v) := by
  rw [lt_top_iff_minkQ, show p + s' • v - (p + s • v) = (s' - s) • v by
    rw [sub_smul]; abel]
  have hpos : 0 < s' - s := sub_pos.2 hss'
  refine ⟨?_, ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul]; exact mul_pos hpos hv.1
  · rw [minkQ_smul]; exact mul_neg_of_pos_of_neg (pow_pos hpos 2) hv.2

/-- An achronal set meets a timelike affine line at most once. -/
theorem eq_of_mem_line_of_isAchronal {S : Set (Minkowski d)} (hS : (minkowski d).IsAchronal S)
    (p : Minkowski d) {v : Minkowski d} (hv : IsFutureTimelike v) {s s' : ℝ}
    (hs : p + s • v ∈ S) (hs' : p + s' • v ∈ S) : s = s' := by
  rcases lt_trichotomy s s' with h | h | h
  · exact absurd (lt_top_line p hv h) (hS _ hs _ hs')
  · exact h
  · exact absurd (lt_top_line p hv h) (hS _ hs' _ hs)

theorem norm_snd_lt_fst {v : Minkowski d} (hv : IsFutureTimelike v) : ‖v.2‖ < v.1 :=
  lt_of_pow_lt_pow_left₀ 2 hv.1.le (minkQ_lt_zero_iff.1 hv.2)

/-- **`bcor:quo`'s "intersects every timelike geodesic", for an entire 1-Lipschitz graph**:
it meets every timelike affine line `{p + s • v}`, `v` future timelike, exactly once. -/
theorem existsUnique_mem_graph_line (hf : LipschitzWith 1 f) (p : Minkowski d)
    {v : Minkowski d} (hv : IsFutureTimelike v) : ∃! s : ℝ, p + s • v ∈ graph f := by
  refine existsUnique_of_exists_of_unique ?_ fun s s' hs hs' =>
    eq_of_mem_line_of_isAchronal (isAchronal_graph_iff.2 hf) p hv hs hs'
  set h : ℝ → ℝ := fun s => (p + s • v).1 - f (p + s • v).2 with hh
  have hcont : Continuous h := by
    simp only [hh]
    exact (continuous_fst.comp (by fun_prop)).sub (hf.continuous.comp (by fun_prop))
  set a := v.1 - ‖v.2‖ with ha
  have hapos : 0 < a := sub_pos.2 (norm_snd_lt_fst hv)
  have hval : ∀ s, h s = p.1 + s * v.1 - f (p.2 + s • v.2) := fun s => by
    simp [hh, smul_eq_mul]
  have hlip : ∀ s, |f (p.2 + s • v.2) - f p.2| ≤ |s| * ‖v.2‖ := fun s => by
    have := abs_sub_le_of_lipschitz hf (p.2 + s • v.2) p.2
    simpa [norm_smul] using this
  have hup : ∀ s, 0 ≤ s → h 0 + s * a ≤ h s := fun s hs => by
    rw [hval, hval]
    have := hlip s
    rw [abs_of_nonneg hs] at this
    simp only [zero_smul, add_zero, zero_mul]
    rw [ha]
    linarith [le_abs_self (f (p.2 + s • v.2) - f p.2)]
  have hdown : ∀ s, s ≤ 0 → h s ≤ h 0 + s * a := fun s hs => by
    rw [hval, hval]
    have := hlip s
    rw [abs_of_nonpos hs] at this
    simp only [zero_smul, add_zero, zero_mul]
    rw [ha]
    linarith [neg_abs_le (f (p.2 + s • v.2) - f p.2)]
  set s₂ := (|h 0| + 1) / a
  have hs₂ : 0 ≤ s₂ := div_nonneg (by positivity) hapos.le
  have e₂ : s₂ * a = |h 0| + 1 := div_mul_cancel₀ _ hapos.ne'
  have h₂ : 0 ≤ h s₂ := by
    have := hup s₂ hs₂; linarith [neg_abs_le (h 0)]
  have h₁ : h (-s₂) ≤ 0 := by
    have := hdown (-s₂) (by linarith)
    rw [neg_mul, e₂] at this; linarith [le_abs_self (h 0)]
  obtain ⟨s, hs⟩ := intermediate_value_univ (-s₂) s₂ hcont ⟨h₁, h₂⟩
  exact ⟨s, sub_eq_zero.1 hs⟩

/-- **An achronal set meeting every vertical line once is the graph of a 1-Lipschitz map.** -/
theorem exists_lipschitz_graph_of_isAchronal {S : Set (Minkowski d)}
    (hS : (minkowski d).IsAchronal S) (hv : ∀ x, ∃! t : ℝ, ((t, x) : Minkowski d) ∈ S) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzWith 1 g ∧ S = graph g := by
  choose g hg using fun x => (hv x).exists
  have hSg : S = graph g := by
    ext p
    refine ⟨fun hp => (hv p.2).unique (show ((p.1, p.2) : Minkowski d) ∈ S from hp) (hg p.2),
      fun hp => ?_⟩
    have : p = (g p.2, p.2) := Prod.ext hp rfl
    rw [this]; exact hg p.2
  exact ⟨g, isAchronal_graph_iff.1 (hSg ▸ hS), hSg⟩

/-- The vertical direction `(1, 0)` is future timelike. -/
theorem isFutureTimelike_vertical : IsFutureTimelike ((1, 0) : Minkowski d) :=
  ⟨one_pos, by simp [minkQ]⟩

/-- **An achronal set meeting every vertical line is the graph of a 1-Lipschitz map**: uniqueness
on vertical lines is automatic from achronality. -/
theorem exists_lipschitz_graph_of_isAchronal_of_exists {S : Set (Minkowski d)}
    (hS : (minkowski d).IsAchronal S) (hv : ∀ x, ∃ t : ℝ, ((t, x) : Minkowski d) ∈ S) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzWith 1 g ∧ S = graph g := by
  refine exists_lipschitz_graph_of_isAchronal hS fun x => ?_
  obtain ⟨t, ht⟩ := hv x
  have key : ∀ r : ℝ, ((r, x) : Minkowski d) = ((0 : ℝ), x) + r • ((1, 0) : Minkowski d) :=
    fun r => Prod.ext (by simp) (by simp)
  refine ⟨t, ht, fun s hs => ?_⟩
  have hs' : ((0 : ℝ), x) + s • ((1, 0) : Minkowski d) ∈ S := by rw [← key]; exact hs
  have ht' : ((0 : ℝ), x) + t • ((1, 0) : Minkowski d) ∈ S := by rw [← key]; exact ht
  exact eq_of_mem_line_of_isAchronal hS _ isFutureTimelike_vertical hs' ht'

/-- **(CC′)(a) of `docs/BARBOT.md`: `S` is an entire 1-Lipschitz graph iff it meets every
timelike affine line exactly once.** -/
theorem exists_lipschitz_graph_iff {S : Set (Minkowski d)} :
    (∃ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzWith 1 g ∧ S = graph g) ↔
      ∀ (p v : Minkowski d), IsFutureTimelike v → ∃! s : ℝ, p + s • v ∈ S := by
  constructor
  · rintro ⟨g, hg, rfl⟩ p v hv
    exact existsUnique_mem_graph_line hg p hv
  · intro h
    have hS : (minkowski d).IsAchronal S := by
      intro x hx y hy hxy
      have hv := lt_top_iff_minkQ.1 hxy
      have h0 : x + (0 : ℝ) • (y - x) ∈ S := by simpa using hx
      have h1 : x + (1 : ℝ) • (y - x) ∈ S := by simpa using hy
      exact zero_ne_one ((h x (y - x) hv).unique h0 h1)
    refine exists_lipschitz_graph_of_isAchronal hS fun x => ?_
    obtain ⟨s, hs, hu⟩ := h ((0 : ℝ), x) (1, 0) isFutureTimelike_vertical
    refine ⟨s, by simpa using hs, fun t ht => ?_⟩
    exact hu t (by simpa using ht)

/-! ### The Cauchy criterion -/

/-- Along `≤`, `t − f(x)` grows by at least `(1 − κ)` times the elapsed time, when `f` is
`κ`-Lipschitz. -/
theorem graphTime_le_of_le {κ : NNReal} (hf : LipschitzWith κ f) {x y : Minkowski d}
    (h : (minkowski d).le ⊤ x y) :
    (1 - κ) * (y.1 - x.1) ≤ (y.1 - f y.2) - (x.1 - f x.2) := by
  have h1 := minkowski_le_top_iff.1 h
  have h2 := abs_sub_le_of_lipschitz hf y.2 x.2
  have h3 : (κ : ℝ) * ‖y.2 - x.2‖ ≤ κ * (y.1 - x.1) := mul_le_mul_of_nonneg_left h1 κ.2
  linarith [le_abs_self (f y.2 - f x.2)]

/-- **`t − f(x)` is strictly increasing along `≤`** when `f` is `κ`-Lipschitz, `κ < 1`. -/
theorem graphTime_lt_of_le {κ : NNReal} (hf : LipschitzWith κ f) (hκ : κ < 1)
    {x y : Minkowski d} (h : (minkowski d).le ⊤ x y) (hne : x ≠ y) :
    x.1 - f x.2 < y.1 - f y.2 := by
  have h1 := minkowski_time_strict.2 x y h hne
  have h2 := graphTime_le_of_le hf h
  have hκ' : (κ : ℝ) < 1 := hκ
  nlinarith

/-- **`t − f(x)` is a Cauchy time function** (`def:cauchy_time_function`) when `f` is
`κ`-Lipschitz, `κ < 1`; `f` need not be bounded (compare `isCauchyTimeFunction_sub`). -/
theorem isCauchyTimeFunction_graphTime {κ : NNReal} (hf : LipschitzWith κ f) (hκ : κ < 1) :
    (minkowski d).IsCauchyTimeFunction fun p => p.1 - f p.2 := by
  have hf1 : ∀ x y, |f x - f y| ≤ dist x y := fun x y => by
    have := abs_sub_le_of_lipschitz (hf.weaken hκ.le) x y
    simpa [dist_eq_norm] using this
  have hκ' : 0 < 1 - (κ : ℝ) := sub_pos.2 hκ
  refine ⟨staticCausality.isTimeFunction_sub f hf1, fun c hc => ⟨?_, ?_⟩⟩
  · have hb := ((tendsto_atBot_add_const_right _ (-(c 0).1)
      (staticCausality.tendsto_time_atBot hc)).const_mul_atBot hκ')
    refine tendsto_atBot_mono' _ ?_
      (tendsto_atBot_add_const_right _ ((c 0).1 - f (c 0).2) hb)
    filter_upwards [eventually_le_atBot 0] with s hs
    have := graphTime_le_of_le hf (hc.1.le_of_le trivial trivial hs)
    simp only [Function.comp]
    linarith
  · have hb := ((tendsto_atTop_add_const_right _ (-(c 0).1)
      (staticCausality.tendsto_time_atTop hc)).const_mul_atTop hκ')
    refine tendsto_atTop_mono' _ ?_
      (tendsto_atTop_add_const_right _ ((c 0).1 - f (c 0).2) hb)
    filter_upwards [eventually_ge_atTop 0] with s hs
    have := graphTime_le_of_le hf (hc.1.le_of_le trivial trivial hs)
    simp only [Function.comp]
    linarith

theorem graph_eq_preimage : graph f = (fun p : Minkowski d => p.1 - f p.2) ⁻¹' {0} := by
  ext p; simp [sub_eq_zero]

/-- **The Cauchy criterion.** If `f : ℝᵈ → ℝ` is `κ`-Lipschitz with `κ < 1`, its graph is a
Cauchy surface of `𝐌ⁿ` in the ETT sense (DEC-14): every inextensible causal curve, over any
interval, meets it exactly once. -/
theorem isCauchySurface_graph {κ : NNReal} (hf : LipschitzWith κ f) (hκ : κ < 1) :
    (minkowski d).IsCauchySurface (graph f) := by
  rw [graph_eq_preimage]
  exact (isCauchyTimeFunction_graphTime hf hκ).isCauchySurface minkowski_causallyArcConnected
    minkowski_stronglyCausal staticCausality.Jminus_ne_singleton
    staticCausality.Jplus_ne_singleton fun x y h hne => graphTime_lt_of_le hf hκ h hne

/-- **Witness** (kb/0011): the horizontal slice `t = 0` is a Cauchy surface. -/
theorem isCauchySurface_graph_zero :
    (minkowski d).IsCauchySurface (graph (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ))) :=
  isCauchySurface_graph (κ := 0) (LipschitzWith.const 0) one_pos

/-! ### Rem 2.2: the hyperboloid is acausal, entire, closed, and not a Cauchy surface -/

/-- The upper hyperboloid `t = √(1 + ‖x‖²)`. -/
noncomputable def hyperboloid (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := √(1 + ‖x‖ ^ 2)

theorem hyperboloid_pos (x : EuclideanSpace ℝ (Fin d)) : 0 < hyperboloid d x :=
  Real.sqrt_pos.2 (by positivity)

theorem hyperboloid_sq (x : EuclideanSpace ℝ (Fin d)) : hyperboloid d x ^ 2 = 1 + ‖x‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- **Rem 2.2's `S = Ω ∩ {Q = −1}`** is the graph of the hyperboloid. -/
theorem graph_hyperboloid : graph (hyperboloid d) = {p | minkQ p = -1 ∧ 0 < p.1} := by
  ext p
  simp only [mem_graph, mem_setOf_eq, minkQ]
  constructor
  · intro h
    refine ⟨?_, h ▸ hyperboloid_pos _⟩
    rw [h, hyperboloid_sq]; ring
  · rintro ⟨h1, h2⟩
    rw [hyperboloid, ← Real.sqrt_sq h2.le]
    congr 1; linarith

theorem continuous_hyperboloid : Continuous (hyperboloid d) := by
  unfold hyperboloid; fun_prop

theorem isClosed_graph_hyperboloid : IsClosed (graph (hyperboloid d)) :=
  isClosed_graph continuous_hyperboloid

/-- The hyperboloid is strictly contracting. -/
theorem abs_hyperboloid_sub_lt {x y : EuclideanSpace ℝ (Fin d)} (hxy : x ≠ y) :
    |hyperboloid d x - hyperboloid d y| < ‖x - y‖ := by
  set a := hyperboloid d x
  set b := hyperboloid d y
  have ha := hyperboloid_pos x
  have hb := hyperboloid_pos y
  have ha2 : a ^ 2 = 1 + ‖x‖ ^ 2 := hyperboloid_sq x
  have hb2 : b ^ 2 = 1 + ‖y‖ ^ 2 := hyperboloid_sq y
  set i := inner ℝ x y
  have hcs : i ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have := abs_real_inner_le_norm x y
    have h2 := pow_le_pow_left₀ (abs_nonneg i) this 2
    rwa [sq_abs, mul_pow] at h2
  have hd : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * i + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  -- `ab > 1 + ⟪x, y⟫`
  have hab : 1 + i < a * b := by
    have hsq : (1 + i) ^ 2 < (a * b) ^ 2 := by
      rw [mul_pow, ha2, hb2]
      nlinarith [pow_pos hpos 2]
    exact (abs_lt_of_sq_lt_sq hsq (by positivity)).trans_le' (le_abs_self _)
  apply abs_lt_of_sq_lt_sq _ hpos.le
  nlinarith

/-- **The hyperboloid is an entire acausal graph.** -/
theorem isAcausal_graph_hyperboloid : (minkowski d).IsAcausal (graph (hyperboloid d)) :=
  isAcausal_graph_iff.2 fun _ _ h => abs_hyperboloid_sub_lt h

theorem lipschitzWith_one_hyperboloid : LipschitzWith 1 (hyperboloid d) :=
  isAchronal_graph_iff.1 (minkowski_isAchronal_of_isAcausal isAcausal_graph_hyperboloid)

/-- A null line `τ ↦ (τ, τe)` stays strictly between the two sheets: `|τ| < √(1 + τ²)`. -/
theorem abs_lt_sqrt_one_add_sq (τ : ℝ) : |τ| < √(1 + τ ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

/-- **Rem 2.2: the hyperboloid is not a Cauchy surface of `𝐌ⁿ`**, `n ≥ 2`: the inextensible null
line `τ ↦ (τ, τe)` misses it. -/
theorem not_isCauchySurface_graph_hyperboloid (hd : 0 < d) :
    ¬ (minkowski d).IsCauchySurface (graph (hyperboloid d)) := by
  intro hS
  obtain ⟨_, ⟨⟨τ, -, rfl⟩, hτ⟩, -⟩ := hS univ _ (minkowski_inextensible_nullLine hd)
  rw [mem_graph] at hτ
  simp only [hyperboloid, norm_smul, norm_unitVec, mul_one, Real.norm_eq_abs, sq_abs] at hτ
  exact (ne_of_lt ((le_abs_self τ).trans_lt (abs_lt_sqrt_one_add_sq τ))) hτ

/-- Hence the hyperboloid is `κ`-Lipschitz for no `κ < 1`. -/
theorem not_lipschitz_hyperboloid (hd : 0 < d) {κ : NNReal} (hκ : κ < 1) :
    ¬ LipschitzWith κ (hyperboloid d) := fun hf =>
  not_isCauchySurface_graph_hyperboloid hd (isCauchySurface_graph hf hκ)

/-- For `d = 0` (Barbot's `n = 1`) Rem 2.2's sentence fails: the hyperboloid is the point `t = 1`
of the line, a Cauchy surface. -/
theorem isCauchySurface_graph_hyperboloid_zero :
    (minkowski 0).IsCauchySurface (graph (hyperboloid 0)) := by
  have : hyperboloid 0 = fun _ => 1 := by
    funext x
    simp [hyperboloid, Subsingleton.elim x 0]
  rw [this]
  exact isCauchySurface_graph (κ := 0) (LipschitzWith.const 1) one_pos

/-- **Finding (Rem 2.2, DEC-27 style).** For `n ≥ 2`, an entire acausal (strictly contracting)
graph need not be a Cauchy surface of `𝐌ⁿ`: (CC′)(a) alone does not give Cauchy. -/
theorem not_forall_isAcausal_graph_isCauchySurface (hd : 0 < d) :
    ¬ ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, (minkowski d).IsAcausal (graph g) →
      (minkowski d).IsCauchySurface (graph g) := fun h =>
  not_isCauchySurface_graph_hyperboloid hd (h _ isAcausal_graph_hyperboloid)

/-! ### Rem 2.2 for either connected component of `{Q < 0}` -/

/-- The lower sheet `Ω₋ ∩ {Q = −1}` is the graph of `−√(1 + ‖x‖²)`. -/
theorem graph_neg_hyperboloid :
    graph (fun x => -hyperboloid d x) = {p | minkQ p = -1 ∧ p.1 < 0} := by
  ext p
  simp only [mem_graph, mem_setOf_eq, minkQ]
  constructor
  · intro h
    refine ⟨?_, by rw [h]; linarith [hyperboloid_pos p.2]⟩
    rw [h, neg_sq, hyperboloid_sq]; ring
  · rintro ⟨h1, h2⟩
    have : -p.1 = hyperboloid d p.2 := by
      rw [hyperboloid, ← Real.sqrt_sq (neg_pos.2 h2).le]
      congr 1; rw [neg_sq]; linarith
    linarith

/-- **Rem 2.2, past sheet**: for `0 < d` the lower hyperboloid is not a Cauchy surface of `𝐌ⁿ`
either; the same null line misses it. -/
theorem not_isCauchySurface_graph_neg_hyperboloid (hd : 0 < d) :
    ¬ (minkowski d).IsCauchySurface (graph (fun x => -hyperboloid d x)) := by
  intro hS
  obtain ⟨_, ⟨⟨τ, -, rfl⟩, hτ⟩, -⟩ := hS univ _ (minkowski_inextensible_nullLine hd)
  rw [mem_graph] at hτ
  simp only [hyperboloid, norm_smul, norm_unitVec, mul_one, Real.norm_eq_abs, sq_abs] at hτ
  have := (neg_abs_le τ).trans_lt' (neg_lt_neg (abs_lt_sqrt_one_add_sq τ))
  exact (ne_of_lt this) hτ.symm

/-- `‖x‖ < t` describes the future timelike cone. -/
theorem isFutureTimelike_iff_norm_lt {v : Minkowski d} : IsFutureTimelike v ↔ ‖v.2‖ < v.1 :=
  ⟨norm_snd_lt_fst, fun h => ⟨(norm_nonneg _).trans_lt h,
    minkQ_lt_zero_iff.2 (pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero)⟩⟩

theorem convex_isFutureTimelike : Convex ℝ {v : Minkowski d | IsFutureTimelike v} := by
  refine convex_iff_forall_pos.2 fun p hp q hq a b ha hb hab => ?_
  simp only [mem_setOf_eq, isFutureTimelike_iff_norm_lt] at hp hq ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  calc ‖a • p.2 + b • q.2‖ ≤ a * ‖p.2‖ + b * ‖q.2‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
    _ < a * p.1 + b * q.1 := add_lt_add (mul_lt_mul_of_pos_left hp ha)
        (mul_lt_mul_of_pos_left hq hb)

/-- In a connected component of `{Q < 0}`, the time coordinate has the sign of the base point. -/
theorem fst_pos_of_mem_connectedComponentIn {p q : Minkowski d} (hp : minkQ p < 0)
    (hq : q ∈ connectedComponentIn {v : Minkowski d | minkQ v < 0} p) : 0 < p.1 * q.1 := by
  have hsub := connectedComponentIn_subset {v : Minkowski d | minkQ v < 0} p
  have hI := (isPreconnected_connectedComponentIn (x := p)
    (F := {v : Minkowski d | minkQ v < 0})).image Prod.fst continuous_fst.continuousOn
  have hp' : p.1 ∈ Prod.fst '' connectedComponentIn {v : Minkowski d | minkQ v < 0} p :=
    mem_image_of_mem _ (mem_connectedComponentIn hp)
  have hq' := mem_image_of_mem Prod.fst hq
  have hne : ∀ r ∈ connectedComponentIn {v : Minkowski d | minkQ v < 0} p, r.1 ≠ 0 :=
    fun r hr h0 => absurd (hsub hr) (not_lt.2 (minkQ_nonneg_of_fst_eq_zero h0))
  have hp0 := hne p (mem_connectedComponentIn hp)
  have hq0 := hne q hq
  by_contra hneg
  have h0 : (0 : ℝ) ∈ Icc (min p.1 q.1) (max p.1 q.1) := by
    rcases lt_or_gt_of_ne hp0 with h1 | h1 <;> rcases lt_or_gt_of_ne hq0 with h2 | h2 <;>
      first
      | exact absurd (mul_pos_of_neg_of_neg h1 h2) hneg
      | exact absurd (mul_pos h1 h2) hneg
      | exact ⟨by simp [h1.le, h2.le], by simp [h1.le, h2.le]⟩
  rcases le_total p.1 q.1 with h | h
  · rw [min_eq_left h, max_eq_right h] at h0
    obtain ⟨r, hr, hr0⟩ := hI.Icc_subset hp' hq' h0
    exact hne r hr hr0
  · rw [min_eq_right h, max_eq_left h] at h0
    obtain ⟨r, hr, hr0⟩ := hI.Icc_subset hq' hp' h0
    exact hne r hr hr0

/-- **The future connected component of `{Q < 0}`** is the open future timelike cone. -/
theorem connectedComponentIn_of_fst_pos {p : Minkowski d} (hp : IsFutureTimelike p) :
    connectedComponentIn {v : Minkowski d | minkQ v < 0} p = {v | IsFutureTimelike v} := by
  refine Subset.antisymm (fun q hq =>
    ⟨?_, connectedComponentIn_subset {v : Minkowski d | minkQ v < 0} p hq⟩) ?_
  · exact pos_of_mul_pos_right (fst_pos_of_mem_connectedComponentIn hp.2 hq) hp.1.le
  · exact convex_isFutureTimelike.isPreconnected.subset_connectedComponentIn hp fun q hq => hq.2

/-- **The past connected component of `{Q < 0}`** is the open past timelike cone. -/
theorem connectedComponentIn_of_fst_neg {p : Minkowski d} (hp : IsFutureTimelike (-p)) :
    connectedComponentIn {v : Minkowski d | minkQ v < 0} p = {v | IsFutureTimelike (-v)} := by
  have hp2 : minkQ p < 0 := by simpa [minkQ_neg] using hp.2
  have hp1 : p.1 < 0 := by simpa using hp.1
  refine Subset.antisymm (fun q hq => ⟨?_, ?_⟩) ?_
  · have := fst_pos_of_mem_connectedComponentIn hp2 hq
    simpa using neg_of_mul_pos_right this hp1.le
  · simpa [minkQ_neg] using connectedComponentIn_subset {v : Minkowski d | minkQ v < 0} p hq
  · have hc : Convex ℝ {v : Minkowski d | IsFutureTimelike (-v)} := by
      have he : {v : Minkowski d | IsFutureTimelike (-v)} =
          -{v : Minkowski d | IsFutureTimelike v} := by
        ext v; simp
      rw [he]; exact (convex_isFutureTimelike (d := d)).neg
    exact hc.isPreconnected.subset_connectedComponentIn hp fun q hq => by
      simpa [minkQ_neg] using hq.2

/-- **Rem 2.2, for either connected component `Ω` of `{Q < 0}`** (`n ≥ 2`): `S = Ω ∩ {Q = −1}`
is not a Cauchy surface of `𝐌ⁿ`. Every component is `connectedComponentIn {Q < 0} p` for some
`p` with `Q(p) < 0`. -/
theorem not_isCauchySurface_connectedComponentIn_inter (hd : 0 < d) {p : Minkowski d}
    (hp : minkQ p < 0) :
    ¬ (minkowski d).IsCauchySurface
      (connectedComponentIn {v : Minkowski d | minkQ v < 0} p ∩ {v | minkQ v = -1}) := by
  rcases isFutureTimelike_or_neg hp with h | h
  · rw [connectedComponentIn_of_fst_pos h]
    have : {v : Minkowski d | IsFutureTimelike v} ∩ {v | minkQ v = -1} =
        graph (hyperboloid d) := by
      rw [graph_hyperboloid]
      ext v
      simp only [mem_inter_iff, mem_setOf_eq, IsFutureTimelike]
      exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, by rw [h.1]; norm_num⟩, h.1⟩⟩
    rw [this]; exact not_isCauchySurface_graph_hyperboloid hd
  · rw [connectedComponentIn_of_fst_neg h]
    have : {v : Minkowski d | IsFutureTimelike (-v)} ∩ {v | minkQ v = -1} =
        graph (fun x => -hyperboloid d x) := by
      rw [graph_neg_hyperboloid]
      ext v
      simp only [mem_inter_iff, mem_setOf_eq, IsFutureTimelike, minkQ_neg, Prod.fst_neg,
        neg_pos]
      exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, by rw [h.1]; norm_num⟩, h.1⟩⟩
    rw [this]; exact not_isCauchySurface_graph_neg_hyperboloid hd

end Flat

end Causal
