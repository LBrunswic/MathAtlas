import Causal.Flat.Cla.SmoothCone
import Causal.Flat.Geroch.Reach

/-!
# `Causal.Flat.Cla.SmoothGlue` — the upper part of finitely many buried past-hyperboloid caps is locally a cone-increasing zero set

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4 and
§11. **No label is marked**: this is the GLOBAL half of the smoothing step of
`Flat/Cla/CompactComplete.lean` (`exists_capEnvelope_succ`, serving `bthm:cauclo`,
`GHFspace.tex:353`, unmarked), the gluing; the construction of the caps is
`Flat/Cla/SmoothCap.lean`. Cited UNMARKED: `[2.4]` Cauchy-complete — l.551–553 (prose, DEC-35, a
reading); Cauchy-compact — l.560–565 (prose). Line numbers are those of the labelled
`papers/barbot/legacy/labeled/GHFspace.tex`.

> A GH spacetime is *Cauchy-complete* if it admits a Cauchy hypersurface where the ambiant
> lorentzian metric restricts as a complete riemanian metric. (l.551–553)

> Among Cauchy-complete spacetimes, there is a remarkable natural family: GH spacetimes with
> *closed* Cauchy hypersurfaces (l.560–561)

The paper treats a closed Cauchy hypersurface as smooth spacelike; the library's Cauchy surfaces
are topological, so a smoothing step is needed, and this file proves its global half.

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

## Main declarations
* Minkowski algebra of PAST hyperboloids (centre `q` in the future): `sqTimeSep_lt_of_le_of_ne`
  (strict reverse triangle inequality: `a ≤ b`, `a ≠ b`, `b ≪ q` ⇒
  `sqTimeSep q b < sqTimeSep q a`, null pairs included), `isConeIncreasingOn_const_sub_sqTimeSep`,
  `exists_isConeIncreasingOn_inf'_const_sub` (a finite `min` of `kᵢ − sqTimeSep qᵢ ·`, centres
  chronologically after `p₀`, is `c`-cone-increasing near `p₀` for one `c < 1`), `sqTimeSep_smul`
  (isometry invariance), `exists_vertical_hyperboloid` (a point strictly on the past side of the
  hyperboloid near `z` lies chronologically below a hyperboloid point near `z`).
* `lt_symm_of_mem_ball`, `le_symm_of_mem_ball` — the cone of a chart ball read in `M`.
* `CapData d M` — a compact cap `C` in a chart `e` of the maximal atlas, on the past hyperboloid
  `{sqTimeSep q · = r}`, with its relative interior `A` (over which `C` is the whole hyperboloid)
  and a domain `U` on which `M`'s relations are read in the chart.
* `isLocallyConeZeroSetAt_of_capData` — **the gluing**: for finitely many caps with closed
  `J⁻(Cₖ)`, relative boundaries buried in `I⁻(K)` (`K = ⋃ Cₖ`) and the push condition, every
  point `x` of the upper part `K ∖ I⁻(K)` has `IsLocallyConeZeroSetAt`: in `chartAt x` the picture
  is `{min_{k : x ∈ Cₖ} (rₖ − sqTimeSep q′ₖ ·) = 0}`, `q′ₖ` the centre transported by the local
  transition isometry.
* `push_of_capData` — the push condition from burial alone (in a flat spacetime): if `x ≤ c ∈ K`,
  `x ≠ c`, then `x ∈ I⁻(K)` (push-up at a buried rim point; at a relatively interior point, a
  point of a causal curve from `x` to `c` close to `c` is strictly on the past side of the
  hyperboloid).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| (none: infrastructure for l.551–565) | `M` charted over `𝐌ⁿ` with the `(Isom(𝐌ⁿ), 𝐌ⁿ)` groupoid; `push_of_capData` on a `FlatSpacetime`; no GH, no Cauchy surface (closedness of `J⁻(Cₖ)` and burial are hypotheses) |

## SCOPE (disclosed)
* The caps are PAST hyperboloids (centre to the future), so the upper part is the upper envelope;
  `SmoothCone`'s `isLocallyConeZeroSetAt_of_inf'_sqTimeSep` (centres in the past) is not used.
* Nothing here constructs caps: `Flat/Cla/SmoothCap.lean` does, over a finite cover of a compact
  acausal Cauchy surface, burying each cap's rim in `I⁻(S)`.
* Namespace `Causal.Flat.Cla`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written for the
Barbot campaign (WP-34e smoothing closer, closing `exists_capEnvelope_succ`).
-/

namespace Causal.Flat.Cla

open Set TopologicalSpace Topology Metric Filter
open scoped NNReal Pointwise

universe u

variable {d : ℕ}

/-! ### Minkowski algebra of past hyperboloids -/

theorem sqTimeSep_eq_neg_minkQ (q p : Minkowski d) : sqTimeSep q p = -minkQ (p - q) := by
  simp only [sqTimeSep, minkQ, Prod.fst_sub, Prod.snd_sub]; ring

/-- **Strict reverse triangle inequality** (past side): if `a ≤ b`, `a ≠ b` and `b ≪ q`, then
`sqTimeSep q b < sqTimeSep q a`. -/
theorem sqTimeSep_lt_of_le_of_ne {a b q : Minkowski d} (hab : (minkowski d).le ⊤ a b)
    (hne : a ≠ b) (hbq : (minkowski d).lt ⊤ b q) : sqTimeSep q b < sqTimeSep q a := by
  have h1 := minkowski_le_top_iff.1 hab
  have h2 := minkowski_lt_top_iff.1 hbq
  have hu : ‖q.2 - a.2‖ ≤ ‖q.2 - b.2‖ + ‖b.2 - a.2‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub q.2 b.2 a.2
    linarith [this]
  have hv0 : 0 ≤ ‖q.2 - b.2‖ := norm_nonneg _
  have hw0 : 0 ≤ ‖b.2 - a.2‖ := norm_nonneg _
  have hu0 : 0 ≤ ‖q.2 - a.2‖ := norm_nonneg _
  have hαβ : 0 < b.1 - a.1 := by
    rcases (hw0.trans h1).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : ‖b.2 - a.2‖ = 0 := le_antisymm (h ▸ h1) hw0
      have h2' : b.2 = a.2 := sub_eq_zero.1 (norm_eq_zero.1 h0)
      exact hne (Prod.ext (by linarith) h2'.symm)
  unfold sqTimeSep
  rw [norm_sub_rev a.2 q.2, norm_sub_rev b.2 q.2]
  rcases le_or_gt ‖q.2 - a.2‖ ‖q.2 - b.2‖ with h | h
  · nlinarith [mul_le_mul h h hu0 hv0]
  · have hk : ‖q.2 - a.2‖ - ‖q.2 - b.2‖ ≤ b.1 - a.1 := by linarith
    have hs : ‖q.2 - a.2‖ + ‖q.2 - b.2‖ < (q.1 - a.1) + (q.1 - b.1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hk (add_nonneg hu0 hv0),
      mul_lt_mul_of_pos_left hs hαβ]

/-- **A past hyperboloid function is cone-increasing with a sign**: `p ↦ k − sqTimeSep q p` is
`c`-cone-increasing on every set of points in the past of `q` inside the cone of slope `c`. -/
theorem isConeIncreasingOn_const_sub_sqTimeSep {c : ℝ} {q : Minkowski d} (k : ℝ)
    {A : Set (Minkowski d)} (hA : ∀ p ∈ A, 0 < q.1 - p.1 ∧ ‖q.2 - p.2‖ ≤ c * (q.1 - p.1)) :
    IsConeIncreasingOn c (fun p => k - sqTimeSep q p) A := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := hA a ha
  obtain ⟨hb0, hb1⟩ := hA b hb
  have hv : ‖q.2 - a.2‖ - ‖q.2 - b.2‖ ≤ ‖b.2 - a.2‖ := by
    have := norm_sub_norm_le (q.2 - a.2) (q.2 - b.2)
    rwa [sub_sub_sub_cancel_left] at this
  have hpos : 0 < (q.1 - a.1) + (q.1 - b.1) := by linarith
  have hsum : 0 ≤ ‖q.2 - a.2‖ + ‖q.2 - b.2‖ := by positivity
  have h1 : c * ‖b.2 - a.2‖ * ((q.1 - a.1) + (q.1 - b.1)) <
      (b.1 - a.1) * ((q.1 - a.1) + (q.1 - b.1)) := mul_lt_mul_of_pos_right hab hpos
  have h2 : (‖q.2 - a.2‖ - ‖q.2 - b.2‖) * (‖q.2 - a.2‖ + ‖q.2 - b.2‖) ≤
      ‖b.2 - a.2‖ * (‖q.2 - a.2‖ + ‖q.2 - b.2‖) := mul_le_mul_of_nonneg_right hv hsum
  have h3 : ‖b.2 - a.2‖ * (‖q.2 - a.2‖ + ‖q.2 - b.2‖) ≤
      ‖b.2 - a.2‖ * (c * ((q.1 - a.1) + (q.1 - b.1))) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  show k - sqTimeSep q a < k - sqTimeSep q b
  unfold sqTimeSep
  rw [norm_sub_rev a.2 q.2, norm_sub_rev b.2 q.2]
  nlinarith [h1, h2, h3]

/-- **Finitely many hyperboloids centred chronologically AFTER `p₀`**: one `c < 1` and one open
neighbourhood `W` of `p₀` on which `p ↦ min_i (k_i − sqTimeSep q_i p)` is `c`-cone-increasing. -/
theorem exists_isConeIncreasingOn_inf'_const_sub {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (q : ι → Minkowski d) (k : ι → ℝ) {p₀ : Minkowski d}
    (h : ∀ i ∈ s, ‖(q i).2 - p₀.2‖ < (q i).1 - p₀.1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∃ W : Set (Minkowski d), IsOpen W ∧ p₀ ∈ W ∧
      IsConeIncreasingOn c (fun p => s.inf' hs fun i => k i - sqTimeSep (q i) p) W := by
  set r : ι → ℝ := fun i => ‖(q i).2 - p₀.2‖ / ((q i).1 - p₀.1) with hrdef
  have hpos : ∀ i ∈ s, 0 < (q i).1 - p₀.1 := fun i hi => (norm_nonneg _).trans_lt (h i hi)
  have hr1 : ∀ i ∈ s, r i < 1 := fun i hi => (div_lt_one (hpos i hi)).2 (h i hi)
  set R := s.sup' hs r with hRdef
  have hR1 : R < 1 := (Finset.sup'_lt_iff hs).2 hr1
  obtain ⟨i₀, hi₀⟩ := hs
  have hR0 : 0 ≤ R := (div_nonneg (norm_nonneg _) (hpos i₀ hi₀).le).trans
    (Finset.le_sup' r hi₀)
  set c := (R + 1) / 2 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hRc : R < c := by rw [hcdef]; linarith
  set W : Set (Minkowski d) :=
    ⋂ i ∈ s, {p | 0 < (q i).1 - p.1 ∧ ‖(q i).2 - p.2‖ < c * ((q i).1 - p.1)} with hWdef
  have hWo : IsOpen W := isOpen_biInter_finset fun i _ =>
    (isOpen_lt continuous_const (continuous_const.sub continuous_fst)).inter
      (isOpen_lt (continuous_const.sub continuous_snd).norm
        (continuous_const.mul (continuous_const.sub continuous_fst)))
  have hp₀ : p₀ ∈ W := by
    refine mem_iInter₂.2 fun i hi => ⟨hpos i hi, ?_⟩
    have hri : r i < c := (Finset.le_sup' r hi).trans_lt hRc
    have : ‖(q i).2 - p₀.2‖ = r i * ((q i).1 - p₀.1) := by
      rw [hrdef]; exact (div_mul_cancel₀ _ (hpos i hi).ne').symm
    rw [this]
    exact mul_lt_mul_of_pos_right hri (hpos i hi)
  have hinc : ∀ i ∈ s, IsConeIncreasingOn c (fun p => k i - sqTimeSep (q i) p) W := by
    intro i hi
    refine isConeIncreasingOn_const_sub_sqTimeSep (k i) fun p hp => ?_
    obtain ⟨h1, h2⟩ := mem_iInter₂.1 hp i hi
    exact ⟨h1, h2.le⟩
  exact ⟨c, hc0, hc1, W, hWo, hp₀, IsConeIncreasingOn.finset_inf' ⟨i₀, hi₀⟩ hinc⟩

/-- **Isometry invariance of the squared time separation.** -/
theorem sqTimeSep_smul (g : isom d) (q z : Minkowski d) :
    sqTimeSep q (g • z) = sqTimeSep (g⁻¹ • q) z := by
  rw [sqTimeSep_eq_neg_minkQ, sqTimeSep_eq_neg_minkQ]
  congr 1
  have := isom_minkQ_sub g (g⁻¹ • q) z
  rwa [smul_inv_smul] at this

/-- **Vertical intermediate value step**: near a point `z` of the past hyperboloid
`{sqTimeSep q · = r}` (`z ≪ q`), every `w` close to `z` strictly on its past side
(`sqTimeSep q w > r`) lies chronologically below a point of the hyperboloid close to `z`, on the
vertical line through `w`. -/
theorem exists_vertical_hyperboloid {q z : Minkowski d} {r : ℝ} (hzq : (minkowski d).lt ⊤ z q)
    (hzr : sqTimeSep q z = r) {η : ℝ} (hη : 0 < η) :
    ∃ ζ > 0, ∀ w : Minkowski d, dist w z < ζ → r < sqTimeSep q w →
      ∃ z' : Minkowski d, dist z' z < η ∧ (minkowski d).lt ⊤ w z' ∧ sqTimeSep q z' = r := by
  have hzq' := minkowski_lt_top_iff.1 hzq
  -- the vertical offset `h`
  set h : ℝ := min (η / 2) (((q.1 - z.1) - ‖q.2 - z.2‖) / 2) with hhdef
  have hh0 : 0 < h := lt_min (by positivity) (by linarith)
  have hhη : h ≤ η / 2 := min_le_left _ _
  have hhq : h ≤ ((q.1 - z.1) - ‖q.2 - z.2‖) / 2 := min_le_right _ _
  set zh : Minkowski d := (z.1 + h, z.2) with hzh
  have hzhq : (minkowski d).lt ⊤ zh q := minkowski_lt_top_iff.2 (by
    show ‖q.2 - z.2‖ < q.1 - (z.1 + h); linarith)
  have hzzh : (minkowski d).le ⊤ z zh := minkowski_le_top_iff.2 (by
    show ‖z.2 - z.2‖ ≤ z.1 + h - z.1; rw [sub_self, norm_zero]; linarith)
  have hne : z ≠ zh := fun he => by
    have := congrArg Prod.fst he; simp [hzh] at this; linarith
  have htop : sqTimeSep q zh < r := hzr ▸ sqTimeSep_lt_of_le_of_ne hzzh hne hzhq
  -- continuity of `w ↦ sqTimeSep q (w + (h, 0))`
  have hcont : Continuous fun w : Minkowski d => sqTimeSep q ((w.1 + h, w.2) : Minkowski d) :=
    (continuous_sqTimeSep q).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  have hev : ∀ᶠ w in 𝓝 z, sqTimeSep q ((w.1 + h, w.2) : Minkowski d) < r :=
    hcont.continuousAt.eventually (gt_mem_nhds htop)
  obtain ⟨ζ₀, hζ₀, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min ζ₀ (η / 2), lt_min hζ₀ (by positivity), fun w hw hwr => ?_⟩
  have hwζ : dist w z < ζ₀ := hw.trans_le (min_le_left _ _)
  have hwη : dist w z < η / 2 := hw.trans_le (min_le_right _ _)
  have hcw : ContinuousOn (fun s : ℝ => sqTimeSep q ((w.1 + s, w.2) : Minkowski d)) (Icc 0 h) :=
    ((continuous_sqTimeSep q).comp
      ((continuous_const.add continuous_id).prodMk continuous_const)).continuousOn
  have h0 : sqTimeSep q ((w.1 + 0, w.2) : Minkowski d) = sqTimeSep q w := by simp
  obtain ⟨s, hs, hsr⟩ := intermediate_value_Icc' hh0.le hcw
    ⟨(hball hwζ).le, by rw [h0]; exact hwr.le⟩
  have hs0 : 0 < s := by
    rcases hs.1.lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [← h'] at hsr; simp only [add_zero, Prod.mk.eta] at hsr; exact hwr.ne' hsr
  refine ⟨(w.1 + s, w.2), ?_, minkowski_lt_top_iff.2 ?_, hsr⟩
  · have : dist ((w.1 + s, w.2) : Minkowski d) w = s := by
      rw [Prod.dist_eq, Real.dist_eq, dist_self]
      simp [abs_of_pos hs0, hs0.le]
    calc dist ((w.1 + s, w.2) : Minkowski d) z
        ≤ dist ((w.1 + s, w.2) : Minkowski d) w + dist w z := dist_triangle _ _ _
      _ < η := by rw [this]; linarith [hs.2]
  · show ‖w.2 - w.2‖ < w.1 + s - w.1
    rw [sub_self, norm_zero]; linarith

/-! ### Chart relations -/

section Charted

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- **A chronological pair of a chart ball is chronological in `M`**: for `e` in the maximal atlas
and a ball `B ⊆ e.target`, `w ≪ z` in `𝐌ⁿ` with `w, z ∈ B` gives `e⁻¹ w ≪ e⁻¹ z` in `M`
(`lt_iff_of_convex` on the convex `B`, then the chart isomorphism on `e⁻¹(B)`). -/
theorem lt_symm_of_mem_ball {e : OpenPartialHomeomorph M (Minkowski d)}
    (he : e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M) {z₀ : Minkowski d} {β : ℝ}
    (hB : ball z₀ β ⊆ e.target) {w z : Minkowski d} (hw : w ∈ ball z₀ β) (hz : z ∈ ball z₀ β)
    (hwz : (minkowski d).lt ⊤ w z) : (flatCausality d M).lt ⊤ (e.symm w) (e.symm z) := by
  have hiso : ChartIso (flatCausality d M) (minkowski d) e := flatCausality_chartIso he
  let UB : Opens M := ⟨e.source ∩ e ⁻¹' ball z₀ β, e.isOpen_inter_preimage isOpen_ball⟩
  have hUBs : UB ≤ chartSource e := fun n hn => hn.1
  have hUBimg : chartImage e UB = ⟨ball z₀ β, isOpen_ball⟩ := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hUBs]
    ext v
    constructor
    · rintro ⟨n, hn, rfl⟩; exact hn.2
    · intro hv
      refine ⟨e.symm v, ⟨e.map_target (hB hv), ?_⟩, e.right_inv (hB hv)⟩
      show e (e.symm v) ∈ ball z₀ β
      rw [e.right_inv (hB hv)]; exact hv
  have hwU : e.symm w ∈ UB := ⟨e.map_target (hB hw), by
    show e (e.symm w) ∈ ball z₀ β; rw [e.right_inv (hB hw)]; exact hw⟩
  have hzU : e.symm z ∈ UB := ⟨e.map_target (hB hz), by
    show e (e.symm z) ∈ ball z₀ β; rw [e.right_inv (hB hz)]; exact hz⟩
  have hball : (minkowski d).lt ⟨ball z₀ β, isOpen_ball⟩ w z :=
    (lt_iff_of_convex (convex_ball z₀ β)).2 ⟨hw, hz, hwz⟩
  refine (flatCausality d M).lt_mono le_top (((hiso UB hUBs _ hwU _ hzU).2).2 ?_)
  rw [hUBimg, e.right_inv (hB hw), e.right_inv (hB hz)]
  exact hball

/-- The causal analogue of `lt_symm_of_mem_ball`. -/
theorem le_symm_of_mem_ball {e : OpenPartialHomeomorph M (Minkowski d)}
    (he : e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M) {z₀ : Minkowski d} {β : ℝ}
    (hB : ball z₀ β ⊆ e.target) {w z : Minkowski d} (hw : w ∈ ball z₀ β) (hz : z ∈ ball z₀ β)
    (hwz : (minkowski d).le ⊤ w z) : (flatCausality d M).le ⊤ (e.symm w) (e.symm z) := by
  have hiso : ChartIso (flatCausality d M) (minkowski d) e := flatCausality_chartIso he
  let UB : Opens M := ⟨e.source ∩ e ⁻¹' ball z₀ β, e.isOpen_inter_preimage isOpen_ball⟩
  have hUBs : UB ≤ chartSource e := fun n hn => hn.1
  have hUBimg : chartImage e UB = ⟨ball z₀ β, isOpen_ball⟩ := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hUBs]
    ext v
    constructor
    · rintro ⟨n, hn, rfl⟩; exact hn.2
    · intro hv
      refine ⟨e.symm v, ⟨e.map_target (hB hv), ?_⟩, e.right_inv (hB hv)⟩
      show e (e.symm v) ∈ ball z₀ β
      rw [e.right_inv (hB hv)]; exact hv
  have hwU : e.symm w ∈ UB := ⟨e.map_target (hB hw), by
    show e (e.symm w) ∈ ball z₀ β; rw [e.right_inv (hB hw)]; exact hw⟩
  have hzU : e.symm z ∈ UB := ⟨e.map_target (hB hz), by
    show e (e.symm z) ∈ ball z₀ β; rw [e.right_inv (hB hz)]; exact hz⟩
  have hball : (minkowski d).le ⟨ball z₀ β, isOpen_ball⟩ w z :=
    (le_iff_of_convex (convex_ball z₀ β)).2 ⟨hw, hz, hwz⟩
  refine (flatCausality d M).le_mono le_top (((hiso UB hUBs _ hwU _ hzU).1).2 ?_)
  rw [hUBimg, e.right_inv (hB hw), e.right_inv (hB hz)]
  exact hball

variable (d M) in
/-- **A past-hyperboloid cap in a chart.** `C ⊆ M` is compact, lies in `U ⊆ e.source`, and its
chart picture lies on the past hyperboloid `{sqTimeSep q · = r}` of the centre `q` (`e c ≪ q`).
`A` is the open set of the chart over which the cap is the WHOLE hyperboloid (its relative
interior): for `p ∈ U` with `e p ∈ A`, `p ∈ C ↔ sqTimeSep q (e p) = r`. On `U` the causal
relations of `M` are read in the chart (`le_chart`, `lt_chart`: in practice `U` lies in a
causally convex set inside the chart's source). -/
structure CapData where
  /-- The chart (of the maximal atlas). -/
  e : OpenPartialHomeomorph M (Minkowski d)
  mem_maximalAtlas : e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M
  /-- The domain on which causal relations are read in the chart. -/
  U : Set M
  U_subset : U ⊆ e.source
  /-- The centre, in the chart. -/
  q : Minkowski d
  /-- The squared radius. -/
  r : ℝ
  /-- The cap. -/
  C : Set M
  /-- The relative interior, in the chart. -/
  A : Set (Minkowski d)
  isCompact_C : IsCompact C
  C_subset : C ⊆ U
  lt_q : ∀ c ∈ C, (minkowski d).lt ⊤ (e c) q
  sqTimeSep_eq : ∀ c ∈ C, sqTimeSep q (e c) = r
  isOpen_A : IsOpen A
  A_subset : ∀ z ∈ A, z ∈ e.target ∧ e.symm z ∈ U
  mem_C_iff : ∀ p ∈ U, e p ∈ A → (p ∈ C ↔ sqTimeSep q (e p) = r)
  le_chart : ∀ p ∈ U, ∀ c ∈ U, (flatCausality d M).le ⊤ p c → (minkowski d).le ⊤ (e p) (e c)
  lt_chart : ∀ p ∈ U, ∀ c ∈ U, (flatCausality d M).lt ⊤ p c → (minkowski d).lt ⊤ (e p) (e c)

/-- A finite infimum vanishes iff one term vanishes and all are nonnegative. -/
theorem finset_inf'_eq_zero_iff {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (v : ι → ℝ) :
    s.inf' hs v = 0 ↔ (∃ k ∈ s, v k = 0) ∧ ∀ k ∈ s, 0 ≤ v k := by
  constructor
  · intro h
    obtain ⟨k, hk, hkv⟩ := Finset.exists_mem_eq_inf' hs v
    exact ⟨⟨k, hk, hkv ▸ h⟩, fun j hj => h ▸ Finset.inf'_le v hj⟩
  · rintro ⟨⟨k, hk, hk0⟩, hall⟩
    exact le_antisymm (hk0 ▸ Finset.inf'_le v hk) ((Finset.le_inf'_iff hs v).2 hall)

/-- **The gluing of finitely many caps.** Let `K` be the union of finitely many caps
(`CapData`), with closed causal pasts `J⁻(Cₖ)`, whose relative boundaries are BURIED in
`I⁻(K)` (`hbur`), and such that no point of `M` lies causally but not chronologically below a
point of `K` without lying in `I⁻(K)` (`hpush`). Then at each point `x` of the upper part
`K ∖ I⁻(K)` the chart picture is locally the zero set of
`min_{k : x ∈ Cₖ} (rₖ − sqTimeSep q′ₖ ·)`, `q′ₖ` the centre read in `chartAt x` through the local
transition isometry: `IsLocallyConeZeroSetAt`. Caps not through `x` are invisible near `x`
(`x ∉ J⁻(Cₖ)`, closed); a cap through `x` has `x` in its relative interior (burial), and there
`p ∈ I⁻(Cₖ) ↔ sqTimeSep qₖ (eₖ p) > rₖ` (reverse triangle one way, the vertical intermediate value
step `exists_vertical_hyperboloid` the other). -/
theorem isLocallyConeZeroSetAt_of_capData {ι : Type*} (s : Finset ι) (P : ι → CapData d M)
    (hJ : ∀ k ∈ s, IsClosed ((flatCausality d M).Jminus ⊤ (P k).C))
    (hbur : ∀ k ∈ s, ∀ c ∈ (P k).C, (P k).e c ∉ (P k).A →
      c ∈ (flatCausality d M).Iminus ⊤ (⋃ j ∈ s, (P j).C))
    (hpush : ∀ c ∈ ⋃ j ∈ s, (P j).C, ∀ x : M, (flatCausality d M).le ⊤ x c → x ≠ c →
      x ∈ (flatCausality d M).Iminus ⊤ (⋃ j ∈ s, (P j).C)) :
    ∀ x ∈ (⋃ j ∈ s, (P j).C) \ (flatCausality d M).Iminus ⊤ (⋃ j ∈ s, (P j).C),
      IsLocallyConeZeroSetAt d
        ((⋃ j ∈ s, (P j).C) \ (flatCausality d M).Iminus ⊤ (⋃ j ∈ s, (P j).C)) x := by
  classical
  set K := ⋃ j ∈ s, (P j).C with hKdef
  set Cs := flatCausality d M with hCs
  intro x hx
  obtain ⟨hxK, hxI⟩ := hx
  set ex := chartAt (Minkowski d) x with hex
  have hxs : x ∈ ex.source := mem_chart_source _ x
  set sx := s.filter fun k => x ∈ (P k).C with hsxdef
  set sf := s.filter fun k => x ∉ (P k).C with hsfdef
  have hsx : sx.Nonempty := by
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hxK
    exact ⟨k, Finset.mem_filter.2 ⟨hk, hxk⟩⟩
  have hmemsx : ∀ {k}, k ∈ sx ↔ k ∈ s ∧ x ∈ (P k).C := fun {k} => Finset.mem_filter
  have hmemsf : ∀ {k}, k ∈ sf ↔ k ∈ s ∧ x ∉ (P k).C := fun {k} => Finset.mem_filter
  -- (1) caps not through `x`: `x ∉ J⁻(Cₖ)`
  have hfar : ∀ k ∈ sf, x ∉ Cs.Jminus ⊤ (P k).C := by
    rintro k hk ⟨c, hc, hxc⟩
    obtain ⟨hks, hxk⟩ := hmemsf.1 hk
    by_cases hxe : x = c
    · exact hxk (hxe ▸ hc)
    · exact hxI (hpush c (mem_biUnion hks hc) x hxc hxe)
  -- (2) caps through `x`: `x` is relatively interior
  have hxA : ∀ k ∈ sx, (P k).e x ∈ (P k).A := by
    intro k hk
    obtain ⟨hks, hxk⟩ := hmemsx.1 hk
    by_contra hcon
    exact hxI (hbur k hks x hxk hcon)
  -- (3) the transitions to `chartAt x`
  have htr : ∀ k ∈ sx, ∃ g : isom d, ∃ O : Opens M, x ∈ O ∧
      O ≤ chartSource ex ⊓ chartSource (P k).e ∧ ∀ z ∈ O, (P k).e z = g • ex z := by
    intro k hk
    have hxk := (P k).U_subset ((P k).C_subset (hmemsx.1 hk).2)
    exact exists_smul_eq_of_mem_gxGroupoid
      ((gxGroupoid (isom d) (Minkowski d)).compatible_of_mem_maximalAtlas
        ((gxGroupoid (isom d) (Minkowski d)).subset_maximalAtlas (chart_mem_atlas _ x))
        (P k).mem_maximalAtlas) hxs hxk
  choose! g O hxO hOle hOeq using htr
  -- (4) the local radii
  have hrad : ∀ k ∈ sx, ∃ ζ > 0, ball ((P k).e x) ζ ⊆ (P k).A ∧
      ∀ p ∈ (P k).e.source, (P k).e p ∈ ball ((P k).e x) ζ →
        (p ∈ Cs.Iminus ⊤ (P k).C ↔ (P k).r < sqTimeSep (P k).q ((P k).e p)) := by
    intro k hk
    obtain ⟨-, hxk⟩ := hmemsx.1 hk
    set Q := P k
    obtain ⟨η, hη, hηA⟩ := Metric.isOpen_iff.1 Q.isOpen_A _ (hxA k hk)
    obtain ⟨ζ, hζ, hIVT⟩ := exists_vertical_hyperboloid (Q.lt_q x hxk) (Q.sqTimeSep_eq x hxk) hη
    have hBt : ball (Q.e x) η ⊆ Q.e.target := fun z hz => (Q.A_subset z (hηA hz)).1
    refine ⟨min ζ η, lt_min hζ hη, (ball_subset_ball (min_le_right _ _)).trans hηA,
      fun p hps hpb => ⟨?_, ?_⟩⟩
    · rintro ⟨c, hc, hpc⟩
      have hpU : p ∈ Q.U := by
        have := (Q.A_subset _ (hηA (ball_subset_ball (min_le_right _ _) hpb))).2
        rwa [Q.e.left_inv hps] at this
      have hlt := Q.lt_chart p hpU c (Q.C_subset hc) hpc
      have hne : Q.e p ≠ Q.e c := fun h => by
        rw [h] at hlt
        have := minkowski_lt_top_iff.1 hlt
        rw [sub_self, norm_zero, sub_self] at this
        exact lt_irrefl _ this
      rw [← Q.sqTimeSep_eq c hc]
      exact sqTimeSep_lt_of_le_of_ne ((minkowski d).le_of_lt hlt) hne (Q.lt_q c hc)
    · intro hr
      obtain ⟨z', hz'd, hpz', hz'r⟩ := hIVT (Q.e p) (hpb.trans_le (min_le_left _ _)) hr
      have hz'A : z' ∈ Q.A := hηA hz'd
      obtain ⟨hz't, hz'U⟩ := Q.A_subset z' hz'A
      have hz'C : Q.e.symm z' ∈ Q.C := by
        refine (Q.mem_C_iff _ hz'U (by rw [Q.e.right_inv hz't]; exact hz'A)).2 ?_
        rw [Q.e.right_inv hz't]; exact hz'r
      refine ⟨_, hz'C, ?_⟩
      have := lt_symm_of_mem_ball Q.mem_maximalAtlas hBt
        (ball_subset_ball (min_le_right _ _) hpb) hz'd hpz'
      rwa [Q.e.left_inv hps] at this
  choose! ζ hζ hζA hζI using hrad
  -- (5) the neighbourhood `N` of `x`
  set N : Set M := (⋂ k ∈ sf, (Cs.Jminus ⊤ (P k).C)ᶜ) ∩
      (⋂ k ∈ sx, ((O k : Set M) ∩ ((P k).e.source ∩ (P k).e ⁻¹' ball ((P k).e x) (ζ k)))) ∩
      ex.source with hNdef
  have hNo : IsOpen N :=
    ((isOpen_biInter_finset fun k hk => (hJ k (hmemsf.1 hk).1).isOpen_compl).inter
      (isOpen_biInter_finset fun k _ => (O k).isOpen.inter
        ((P k).e.isOpen_inter_preimage isOpen_ball))).inter ex.open_source
  have hxN : x ∈ N := by
    refine ⟨⟨mem_iInter₂.2 fun k hk => hfar k hk, mem_iInter₂.2 fun k hk =>
      ⟨hxO k hk, (hOle k hk (hxO k hk)).2, mem_ball_self (hζ k hk)⟩⟩, hxs⟩
  -- (6) membership on `N`
  have hNsx : ∀ p ∈ N, ∀ k ∈ sx, p ∈ O k ∧ p ∈ (P k).e.source ∧
      (P k).e p ∈ ball ((P k).e x) (ζ k) := fun p hp k hk => mem_iInter₂.1 hp.1.2 k hk
  have hNsf : ∀ p ∈ N, ∀ k ∈ sf, p ∉ Cs.Jminus ⊤ (P k).C := fun p hp k hk =>
    mem_iInter₂.1 hp.1.1 k hk
  have hNU : ∀ p ∈ N, ∀ k ∈ sx, p ∈ (P k).U := by
    intro p hp k hk
    obtain ⟨-, hps, hpb⟩ := hNsx p hp k hk
    have := ((P k).A_subset _ (hζA k hk hpb)).2
    rwa [(P k).e.left_inv hps] at this
  have hsxf : ∀ k ∈ s, k ∉ sx → k ∈ sf := fun k hk hn =>
    hmemsf.2 ⟨hk, fun hxk => hn (hmemsx.2 ⟨hk, hxk⟩)⟩
  have hinK : ∀ p ∈ N, (p ∈ K ↔ ∃ k ∈ sx, sqTimeSep (P k).q ((P k).e p) = (P k).r) := by
    intro p hp
    constructor
    · intro hpK
      obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.1 hpK
      have hksx : k ∈ sx := by
        by_contra hn
        exact hNsf p hp k (hsxf k hk hn) (Cs.subset_Jminus (U := ⊤) (fun _ _ => trivial) hpk)
      obtain ⟨-, -, hpb⟩ := hNsx p hp k hksx
      exact ⟨k, hksx, ((P k).mem_C_iff p (hNU p hp k hksx) (hζA k hksx hpb)).1 hpk⟩
    · rintro ⟨k, hk, hkr⟩
      obtain ⟨-, -, hpb⟩ := hNsx p hp k hk
      exact mem_biUnion (hmemsx.1 hk).1
        (((P k).mem_C_iff p (hNU p hp k hk) (hζA k hk hpb)).2 hkr)
  have hinI : ∀ p ∈ N,
      (p ∈ Cs.Iminus ⊤ K ↔ ∃ k ∈ sx, (P k).r < sqTimeSep (P k).q ((P k).e p)) := by
    intro p hp
    constructor
    · rintro ⟨c, hcK, hpc⟩
      obtain ⟨k, hk, hck⟩ := mem_iUnion₂.1 hcK
      have hksx : k ∈ sx := by
        by_contra hn
        exact hNsf p hp k (hsxf k hk hn) (Cs.Iminus_subset_Jminus ⟨c, hck, hpc⟩)
      obtain ⟨-, hps, hpb⟩ := hNsx p hp k hksx
      exact ⟨k, hksx, (hζI k hksx p hps hpb).1 ⟨c, hck, hpc⟩⟩
    · rintro ⟨k, hk, hkr⟩
      obtain ⟨-, hps, hpb⟩ := hNsx p hp k hk
      obtain ⟨c, hc, hpc⟩ := (hζI k hk p hps hpb).2 hkr
      exact ⟨c, mem_biUnion (hmemsx.1 hk).1 hc, hpc⟩
  -- (7) the centres read in `chartAt x`
  set q' : ι → Minkowski d := fun k => (g k)⁻¹ • (P k).q with hq'
  have hsep : ∀ p ∈ N, ∀ k ∈ sx,
      sqTimeSep (P k).q ((P k).e p) = sqTimeSep (q' k) (ex p) := by
    intro p hp k hk
    rw [hOeq k hk p (hNsx p hp k hk).1, sqTimeSep_smul]
  have hcent : ∀ k ∈ sx, ‖(q' k).2 - (ex x).2‖ < (q' k).1 - (ex x).1 := by
    intro k hk
    have h1 := (P k).lt_q x (hmemsx.1 hk).2
    rw [hOeq k hk x (hxO k hk)] at h1
    have h2 : (minkowski d).lt ⊤ (ex x) (q' k) := by
      rw [← isom_lt_top_iff (g k)]
      simpa [hq'] using h1
    exact minkowski_lt_top_iff.1 h2
  obtain ⟨c, hc0, hc1, W', hW'o, hxW', hinc⟩ :=
    exists_isConeIncreasingOn_inf'_const_sub sx hsx q' (fun k => (P k).r) hcent
  refine ⟨ex '' N ∩ W', fun z => sx.inf' hsx fun k => (P k).r - sqTimeSep (q' k) z, c, hc0, hc1,
    (ex.isOpen_image_of_subset_source hNo (fun p hp => hp.2)).inter hW'o,
    ⟨⟨x, hxN, rfl⟩, hxW'⟩, fun z hz => ?_, ?_, hinc.mono le_rfl inter_subset_right, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := hz.1; exact ex.map_source hp.2
  · exact ContinuousOn.finset_inf'_apply hsx fun k _ =>
      (continuous_const.sub (continuous_sqTimeSep _)).continuousOn
  · rintro z ⟨⟨p, hp, rfl⟩, -⟩
    have hiff : ex p ∈ ex '' ((K \ Cs.Iminus ⊤ K) ∩ ex.source) ↔ p ∈ K \ Cs.Iminus ⊤ K := by
      constructor
      · rintro ⟨p', ⟨hp'H, hp's⟩, he⟩
        rwa [← ex.injOn hp's hp.2 he]
      · intro h; exact ⟨p, ⟨h, hp.2⟩, rfl⟩
    rw [hiff, finset_inf'_eq_zero_iff, Set.mem_sdiff, hinK p hp, hinI p hp]
    constructor
    · rintro ⟨⟨k, hk, hkr⟩, hall⟩
      refine ⟨⟨k, hk, by rw [← hsep p hp k hk, hkr, sub_self]⟩, fun j hj => ?_⟩
      have hj' : ¬ (P j).r < sqTimeSep (P j).q ((P j).e p) := fun h => hall ⟨j, hj, h⟩
      rw [← hsep p hp j hj]; linarith [not_lt.1 hj']
    · rintro ⟨⟨k, hk, hk0⟩, hall⟩
      refine ⟨⟨k, hk, by rw [hsep p hp k hk]; linarith⟩, ?_⟩
      rintro ⟨j, hj, hjr⟩
      have := hall j hj
      rw [← hsep p hp j hj] at this
      linarith

/-- **Near a relatively interior point of a cap, its strict past side is in `I⁻` of the cap.** -/
theorem CapData.exists_ball_mem_Iminus (P : CapData d M) {x₀ : M} (hx₀ : x₀ ∈ P.C)
    (hA : P.e x₀ ∈ P.A) :
    ∃ ζ > 0, ball (P.e x₀) ζ ⊆ P.A ∧ ∀ p ∈ P.e.source, P.e p ∈ ball (P.e x₀) ζ →
      P.r < sqTimeSep P.q (P.e p) → p ∈ (flatCausality d M).Iminus ⊤ P.C := by
  obtain ⟨η, hη, hηA⟩ := Metric.isOpen_iff.1 P.isOpen_A _ hA
  obtain ⟨ζ, hζ, hIVT⟩ := exists_vertical_hyperboloid (P.lt_q x₀ hx₀) (P.sqTimeSep_eq x₀ hx₀) hη
  have hBt : ball (P.e x₀) η ⊆ P.e.target := fun z hz => (P.A_subset z (hηA hz)).1
  refine ⟨min ζ η, lt_min hζ hη, (ball_subset_ball (min_le_right _ _)).trans hηA,
    fun p hps hpb hr => ?_⟩
  obtain ⟨z', hz'd, hpz', hz'r⟩ := hIVT (P.e p) (hpb.trans_le (min_le_left _ _)) hr
  have hz'A : z' ∈ P.A := hηA hz'd
  obtain ⟨hz't, hz'U⟩ := P.A_subset z' hz'A
  have hz'C : P.e.symm z' ∈ P.C := by
    refine (P.mem_C_iff _ hz'U (by rw [P.e.right_inv hz't]; exact hz'A)).2 ?_
    rw [P.e.right_inv hz't]; exact hz'r
  refine ⟨_, hz'C, ?_⟩
  have := lt_symm_of_mem_ball P.mem_maximalAtlas hBt
    (ball_subset_ball (min_le_right _ _) hpb) hz'd hpz'
  rwa [P.e.left_inv hps] at this

end Charted

/-- **Causal-but-not-chronological pasts of buried caps are chronological** (the `hpush`
hypothesis of `isLocallyConeZeroSetAt_of_capData`). If `x ≤ c ∈ K`, `x ≠ c`: when `c` is on the
relative boundary of its cap, `c ∈ I⁻(K)` (burial) and push-up gives `x ∈ I⁻(K)`; when `c` is
relatively interior, a point `x′` of a causal curve from `x` to `c`, close to `c` and `≠ c`, is
strictly on the past side of the hyperboloid in the chart (strict reverse triangle inequality),
hence below a point of the cap (`CapData.exists_ball_mem_Iminus`), and `x ≤ x′ ≪ c′`. -/
theorem push_of_capData {M : FlatSpacetime.{u} d} {ι : Type*} (s : Finset ι)
    (P : ι → CapData d M)
    (hbur : ∀ k ∈ s, ∀ c ∈ (P k).C, (P k).e c ∉ (P k).A →
      c ∈ (flatCausality d M).Iminus ⊤ (⋃ j ∈ s, (P j).C)) :
    ∀ c ∈ ⋃ j ∈ s, (P j).C, ∀ x : M, (flatCausality d M).le ⊤ x c → x ≠ c →
      x ∈ (flatCausality d M).Iminus ⊤ (⋃ j ∈ s, (P j).C) := by
  intro c hcK x hxc hne
  have hpush := flatCausality_pushUp (N := M)
  obtain ⟨k, hk, hck⟩ := mem_iUnion₂.1 hcK
  set Q := P k
  by_cases hA : Q.e c ∈ Q.A
  swap
  · obtain ⟨c', hc', hcc'⟩ := hbur k hk c hck hA
    exact ⟨c', hc', hpush.lt_of_le_of_lt hxc hcc'⟩
  obtain ⟨ζ, hζ, hζA, hζI⟩ := Q.exists_ball_mem_Iminus hck hA
  have hcs : c ∈ Q.e.source := Q.U_subset (Q.C_subset hck)
  -- a point of a causal curve from `x` to `c`, close to `c`, not `c`
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := ((flatCausality_causallyArcConnected d M) ⊤ le_rfl x c).1.1 hxc
  have hγc : ContinuousOn γ (Icc 0 1) := CurveOn.continuousOn (flatCausality d M).isRelFamily_le hγ
  set N : Set M := Q.e.source ∩ Q.e ⁻¹' ball (Q.e c) ζ with hNdef
  have hNo : IsOpen N := Q.e.isOpen_inter_preimage isOpen_ball
  have hcN : c ∈ N := ⟨hcs, mem_ball_self hζ⟩
  set S₀ : Set ℝ := Icc 0 1 ∩ γ ⁻¹' {c} with hS₀
  have hS₀c : IsClosed S₀ := hγc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have h1S : (1 : ℝ) ∈ S₀ := ⟨⟨zero_le_one, le_rfl⟩, hγ1⟩
  have hbdd : BddBelow S₀ := ⟨0, fun t ht => ht.1.1⟩
  set σ := sInf S₀ with hσ
  have hσS : σ ∈ S₀ := hS₀c.csInf_mem ⟨1, h1S⟩ hbdd
  have hσ0 : 0 < σ := by
    rcases hσS.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hne; rw [← hγ0, h]; exact hσS.2
  obtain ⟨ε, hε, hεN⟩ : ∃ ε > 0, ∀ t ∈ Icc (0 : ℝ) 1, dist t σ < ε → γ t ∈ N := by
    have hcw := hγc σ hσS.1
    have : γ ⁻¹' N ∈ 𝓝[Icc 0 1] σ := hcw.preimage_mem_nhdsWithin
      (hNo.mem_nhds (by rw [show γ σ = c from hσS.2]; exact hcN))
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 this
    exact ⟨ε, hε, fun t ht hd => hεs ⟨hd, ht⟩⟩
  set t := max (σ - ε / 2) (σ / 2) with htdef
  have htσ : t < σ := max_lt (by linarith) (by linarith)
  have ht0 : 0 ≤ t := le_max_of_le_right (by linarith)
  have ht1 : t ≤ 1 := htσ.le.trans hσS.1.2
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have htN : γ t ∈ N := hεN t htI (by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : σ - ε / 2 ≤ t := le_max_left _ _
    linarith)
  have hγtc : γ t ≠ c := fun h => by
    have : σ ≤ t := csInf_le hbdd ⟨htI, h⟩
    linarith
  have hxγ : (flatCausality d M).le ⊤ x (γ t) := by
    rw [← hγ0]; exact hγ.le_of_le le_rfl ht0 ht1
  have hγc' : (flatCausality d M).le ⊤ (γ t) c := by
    rw [← hγ1]; exact hγ.le_of_le ht0 ht1 le_rfl
  -- the chart picture
  have hγU : γ t ∈ Q.U := by
    have := (Q.A_subset _ (hζA htN.2)).2
    rwa [Q.e.left_inv htN.1] at this
  have hle := Q.le_chart _ hγU c (Q.C_subset hck) hγc'
  have hne' : Q.e (γ t) ≠ Q.e c := fun h => hγtc (Q.e.injOn htN.1 hcs h)
  have hr : Q.r < sqTimeSep Q.q (Q.e (γ t)) := by
    rw [← Q.sqTimeSep_eq c hck]
    exact sqTimeSep_lt_of_le_of_ne hle hne' (Q.lt_q c hck)
  obtain ⟨c', hc', hγc''⟩ := hζI (γ t) htN.1 htN.2 hr
  exact ⟨c', mem_biUnion hk hc', hpush.lt_of_le_of_lt hxγ hγc''⟩

end Causal.Flat.Cla
