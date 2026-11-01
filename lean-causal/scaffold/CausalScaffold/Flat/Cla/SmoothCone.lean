import CausalScaffold.Flat.CauchyComplete

/-!
# `CausalScaffold.Flat.Cla.SmoothCone` — zero sets of cone-increasing functions are spacelike Lipschitz

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4 and
§11. **No label is marked**: these are the LOCAL, analytic half of the smoothing step of
`Flat/Cla/CompactComplete.lean` (`exists_nonempty_isSpacelikeLipschitz_succ`, serving
`bthm:cauclo`, `GHFspace.tex:353`, unmarked). Cited UNMARKED: `[2.4]` Cauchy-complete —
l.551–553 (prose, DEC-35, a reading). Line numbers are those of the labelled
`papers/barbot/legacy/labeled/GHFspace.tex`.

> A GH spacetime is *Cauchy-complete* if it admits a Cauchy hypersurface where the ambiant
> lorentzian metric restricts as a complete riemanian metric. (l.551–553)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

The envelope of hyperboloids (the smoothing of a topological Cauchy surface) is, in a chart, the
zero set of a finite max or min of the functions `sqTimeSep q p = (p.1 − q.1)² − ‖p.2 − q.2‖²`
(`= −minkQ (p − q)`). This file proves, with no `sorry`, that such a zero set is a spacelike
Lipschitz hypersurface in the sense of `IsSpacelikeLipschitz` (contract (f): `c < 1` point by
point), through one derivative-free notion: `f` is **`c`-cone-increasing** on `A` if
`f a < f b` whenever `c ‖b.2 − a.2‖ < b.1 − a.1`. A zero set of a continuous `c`-cone-increasing
function with `c < 1` is, near each of its points, the graph of a `c`-Lipschitz function
(intermediate value theorem on vertical segments, uniqueness and the Lipschitz bound from the cone
condition itself), and cone-increasing functions are stable under finite `max` and `min`.

## Main declarations
* `IsConeIncreasingOn c f A` — the cone condition; `.mono`, `.sub_const`, `.finset_sup'`,
  `.finset_inf'`.
* `sqTimeSep q p` — the squared time separation; `isConeIncreasingOn_sqTimeSep`: it is
  `c`-cone-increasing on any `A` whose points lie in the future of `q` with
  `‖p.2 − q.2‖ ≤ c (p.1 − q.1)` (no convexity: `Δ(sqTimeSep) = (Z₀)(s) − ⟨Z_x, v⟩` with `Z = a + b − 2q`).
* `exists_isConeIncreasingOn_sup'_inf'` — a finite family of hyperboloids whose centres are all
  chronologically before `p₀`: their `max` and `min` (with offsets) are `c`-cone-increasing on an
  open neighbourhood of `p₀`, for one `c < 1`.
* `exists_isSpacelikeLipschitzIn_zeroSet` — in `𝐌ⁿ`: a continuous `c`-cone-increasing `f`
  (`c < 1`) on an open `W`, with `f p₀ = 0`, has a sup-norm ball `V ∋ p₀` in which
  `{f = 0} ∩ V` is `IsSpacelikeLipschitzIn V`.
* `IsLocallyConeZeroSetAt d H x` — near `chartAt x x` the chart picture of `H` is the zero set of
  a continuous `c`-cone-increasing function, `0 ≤ c < 1`.
* `isSpacelikeLipschitz_of_locally_coneIncreasing` — on `M` charted over `𝐌ⁿ`: if
  `IsLocallyConeZeroSetAt d H x` at each `x ∈ H`, then `IsSpacelikeLipschitz d H`.
* `isLocallyConeZeroSetAt_of_sup'_sqTimeSep`, `isLocallyConeZeroSetAt_of_inf'_sqTimeSep` — the
  local data from a finite max (future envelope `sup_y τ(y, ·) = ε`) or min (upper boundary of a
  union of pasts of future-hyperboloid caps) of hyperboloid functions centred chronologically
  before the point.
* `isCompact_diff_Iminus`, `nonempty_diff_Iminus` — for any causality: the UPPER PART
  `K ∖ I⁻(K)` of a compact `K` is compact, and nonempty when `K` is and no point is
  chronologically related to itself (a finite subcover by `I⁻(kᵢ)` closes a chronological chain).
  This is the intrinsic gluing of finitely many caps: no time separation on `M`, no achronal
  boundary theory, no closedness of `J⁻(K)`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| (none: infrastructure for l.551–553) | any `M` charted over `𝐌ⁿ`; no groupoid, no Hausdorff, no GH; the upper-part lemmas for any causality, chronology assumed |

## SCOPE (disclosed)
* Nothing here constructs the envelope on a flat spacetime: the global half of the smoothing step
  (a nonempty compact `K` — finitely many hyperboloid caps — whose upper part `K ∖ I⁻(K)` has
  such chart pictures) is `Flat/Cla/SmoothGlue.lean` (the gluing) and `Flat/Cla/SmoothCap.lean`
  (the caps), which close `CompactComplete.lean`'s `exists_capEnvelope_succ`. They use PAST
  hyperboloids (centres to the future) and their own `min` lemma; the two hyperboloid lemmas
  here with centres in the past (`isLocallyConeZeroSetAt_of_sup'_sqTimeSep`, `_of_inf'_`) are not
  used downstream.
* The frame in `locGraph` is always `1`: the chart's own frame. A hyperboloid read in another chart
  is a hyperboloid (isometries preserve `minkQ`), so no frame change is needed downstream.
* Namespace `Causal.Flat.Cla`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written for the
Barbot campaign (WP-34e smoothing closer pass on `CompactComplete`).
-/

namespace Causal.Flat.Cla

open Set TopologicalSpace Topology Metric
open scoped NNReal Pointwise

variable {d : ℕ}

/-! ### The cone condition -/

/-- **`f` is `c`-cone-increasing on `A`**: `f a < f b` whenever `b` lies above `a` within the cone
of slope `c`, i.e. `c ‖b.2 − a.2‖ < b.1 − a.1`. For `c < 1` the cone contains the causal cone. -/
def IsConeIncreasingOn (c : ℝ) (f : Minkowski d → ℝ) (A : Set (Minkowski d)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, c * ‖b.2 - a.2‖ < b.1 - a.1 → f a < f b

theorem IsConeIncreasingOn.mono {c c' : ℝ} {f : Minkowski d → ℝ} {A B : Set (Minkowski d)}
    (h : IsConeIncreasingOn c f A) (hc : c ≤ c') (hBA : B ⊆ A) : IsConeIncreasingOn c' f B :=
  fun a ha b hb hab =>
    h a (hBA ha) b (hBA hb) (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hab)

theorem IsConeIncreasingOn.sub_const {c : ℝ} {f : Minkowski d → ℝ} {A : Set (Minkowski d)}
    (h : IsConeIncreasingOn c f A) (k : ℝ) : IsConeIncreasingOn c (fun p => f p - k) A :=
  fun a ha b hb hab => sub_lt_sub_right (h a ha b hb hab) k

/-- **Finite maxima** of `c`-cone-increasing functions are `c`-cone-increasing. -/
theorem IsConeIncreasingOn.finset_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {c : ℝ}
    {f : ι → Minkowski d → ℝ} {A : Set (Minkowski d)} (h : ∀ i ∈ s, IsConeIncreasingOn c (f i) A) :
    IsConeIncreasingOn c (fun p => s.sup' hs fun i => f i p) A := by
  intro a ha b hb hab
  obtain ⟨i, hi, hia⟩ := Finset.exists_mem_eq_sup' hs (fun i => f i a)
  show s.sup' hs (fun i => f i a) < s.sup' hs (fun i => f i b)
  rw [hia]
  exact (h i hi a ha b hb hab).trans_le (Finset.le_sup' (fun i => f i b) hi)

/-- **Finite minima** of `c`-cone-increasing functions are `c`-cone-increasing. -/
theorem IsConeIncreasingOn.finset_inf' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {c : ℝ}
    {f : ι → Minkowski d → ℝ} {A : Set (Minkowski d)} (h : ∀ i ∈ s, IsConeIncreasingOn c (f i) A) :
    IsConeIncreasingOn c (fun p => s.inf' hs fun i => f i p) A := by
  intro a ha b hb hab
  obtain ⟨i, hi, hib⟩ := Finset.exists_mem_eq_inf' hs (fun i => f i b)
  show s.inf' hs (fun i => f i a) < s.inf' hs (fun i => f i b)
  rw [hib]
  exact (Finset.inf'_le (fun i => f i a) hi).trans_lt (h i hi a ha b hb hab)

/-! ### Hyperboloids -/

/-- **The squared time separation** `(p.1 − q.1)² − ‖p.2 − q.2‖² = −minkQ (p − q)` of `p` from the
centre `q`; its positive level sets in `I⁺(q)` are the future hyperboloids of `q`. -/
noncomputable def sqTimeSep (q p : Minkowski d) : ℝ := (p.1 - q.1) ^ 2 - ‖p.2 - q.2‖ ^ 2

theorem continuous_sqTimeSep (q : Minkowski d) : Continuous (sqTimeSep q) :=
  ((continuous_fst.sub continuous_const).pow 2).sub
    (((continuous_snd.sub continuous_const).norm).pow 2)

/-- **A hyperboloid function is cone-increasing** on every set of points lying in the future of
its centre `q` inside the cone of slope `c`: with `α = a.1 − q.1`, `β = b.1 − q.1`,
`Δ = (β − α)(β + α) − (‖b.2 − q.2‖ − ‖a.2 − q.2‖)(‖b.2 − q.2‖ + ‖a.2 − q.2‖)
  ≥ (α + β)(b.1 − a.1 − c ‖b.2 − a.2‖) > 0`. No convexity of `A` is used. -/
theorem isConeIncreasingOn_sqTimeSep {c : ℝ} {q : Minkowski d}
    {A : Set (Minkowski d)} (hA : ∀ p ∈ A, 0 < p.1 - q.1 ∧ ‖p.2 - q.2‖ ≤ c * (p.1 - q.1)) :
    IsConeIncreasingOn c (sqTimeSep q) A := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := hA a ha
  obtain ⟨hb0, hb1⟩ := hA b hb
  have hv : ‖b.2 - q.2‖ - ‖a.2 - q.2‖ ≤ ‖b.2 - a.2‖ := by
    have := norm_sub_norm_le (b.2 - q.2) (a.2 - q.2)
    rwa [sub_sub_sub_cancel_right] at this
  have hs : b.1 - a.1 = (b.1 - q.1) - (a.1 - q.1) := by ring
  have hpos : 0 < (a.1 - q.1) + (b.1 - q.1) := by linarith
  have hsum : 0 ≤ ‖b.2 - q.2‖ + ‖a.2 - q.2‖ := by positivity
  have h1 : c * ‖b.2 - a.2‖ * ((a.1 - q.1) + (b.1 - q.1)) <
      (b.1 - a.1) * ((a.1 - q.1) + (b.1 - q.1)) := mul_lt_mul_of_pos_right hab hpos
  have h2 : (‖b.2 - q.2‖ - ‖a.2 - q.2‖) * (‖b.2 - q.2‖ + ‖a.2 - q.2‖) ≤
      ‖b.2 - a.2‖ * (‖b.2 - q.2‖ + ‖a.2 - q.2‖) := mul_le_mul_of_nonneg_right hv hsum
  have h3 : ‖b.2 - a.2‖ * (‖b.2 - q.2‖ + ‖a.2 - q.2‖) ≤
      ‖b.2 - a.2‖ * (c * ((a.1 - q.1) + (b.1 - q.1))) :=
    mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  unfold sqTimeSep
  rw [hs] at h1
  nlinarith [h1, h2, h3]

/-- **Finitely many hyperboloids centred chronologically before `p₀`**: one `c < 1` and one open
neighbourhood `W` of `p₀` on which their `max` and their `min` (with arbitrary offsets) are
`c`-cone-increasing. (`c` is the mean of `1` and the largest ratio `‖p₀.2 − qᵢ.2‖ / (p₀.1 − qᵢ.1)`;
`W` is the intersection of the open cones of slope `c` over the centres.) -/
theorem exists_isConeIncreasingOn_sup'_inf' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (q : ι → Minkowski d) (k : ι → ℝ) {p₀ : Minkowski d}
    (h : ∀ i ∈ s, ‖p₀.2 - (q i).2‖ < p₀.1 - (q i).1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∃ W : Set (Minkowski d), IsOpen W ∧ p₀ ∈ W ∧
      IsConeIncreasingOn c (fun p => s.sup' hs fun i => sqTimeSep (q i) p - k i) W ∧
      IsConeIncreasingOn c (fun p => s.inf' hs fun i => sqTimeSep (q i) p - k i) W := by
  set r : ι → ℝ := fun i => ‖p₀.2 - (q i).2‖ / (p₀.1 - (q i).1) with hrdef
  have hpos : ∀ i ∈ s, 0 < p₀.1 - (q i).1 := fun i hi => (norm_nonneg _).trans_lt (h i hi)
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
    ⋂ i ∈ s, {p | 0 < p.1 - (q i).1 ∧ ‖p.2 - (q i).2‖ < c * (p.1 - (q i).1)} with hWdef
  have hWo : IsOpen W := isOpen_biInter_finset fun i _ =>
    (isOpen_lt continuous_const (continuous_fst.sub continuous_const)).inter
      (isOpen_lt (continuous_snd.sub continuous_const).norm
        (continuous_const.mul (continuous_fst.sub continuous_const)))
  have hp₀ : p₀ ∈ W := by
    refine mem_iInter₂.2 fun i hi => ⟨hpos i hi, ?_⟩
    have hri : r i < c := (Finset.le_sup' r hi).trans_lt hRc
    have : ‖p₀.2 - (q i).2‖ = r i * (p₀.1 - (q i).1) := by
      rw [hrdef]; exact (div_mul_cancel₀ _ (hpos i hi).ne').symm
    rw [this]
    exact mul_lt_mul_of_pos_right hri (hpos i hi)
  have hinc : ∀ i ∈ s, IsConeIncreasingOn c (fun p => sqTimeSep (q i) p - k i) W := by
    intro i hi
    refine (isConeIncreasingOn_sqTimeSep fun p hp => ?_).sub_const (k i)
    obtain ⟨h1, h2⟩ := mem_iInter₂.1 hp i hi
    exact ⟨h1, h2.le⟩
  exact ⟨c, hc0, hc1, W, hWo, hp₀, IsConeIncreasingOn.finset_sup' ⟨i₀, hi₀⟩ hinc,
    IsConeIncreasingOn.finset_inf' ⟨i₀, hi₀⟩ hinc⟩

/-! ### Zero sets in `𝐌ⁿ` -/

/-- **The zero set of a continuous `c`-cone-increasing function, `c < 1`, is a spacelike Lipschitz
hypersurface near each of its points.** With `ρ` a sup-norm radius at `p₀` inside `W` and
`δ = ρ / 2`, `V` is the sup-norm ball of radius `δ`: over each `x` of the spatial ball `U` the
vertical segment `[p₀.1 − δ, p₀.1 + δ] × {x}` changes sign (cone condition against `p₀`, as
`c ‖x − p₀.2‖ < δ`), so carries a zero `F x` (intermediate value theorem), unique (vertical
pairs satisfy the cone condition); `F` is `c`-Lipschitz on `U` (a pair violating it satisfies the
cone condition); and `{f = 0} ∩ V = V ∩ graphOver U F`, achronal since `c ≤ 1`. -/
theorem exists_isSpacelikeLipschitzIn_zeroSet {W : Set (Minkowski d)} (hW : IsOpen W)
    {f : Minkowski d → ℝ} (hf : ContinuousOn f W) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hinc : IsConeIncreasingOn c f W) {p₀ : Minkowski d} (hp₀ : p₀ ∈ W) (hf₀ : f p₀ = 0) :
    ∃ V : Opens (Minkowski d), p₀ ∈ V ∧ (V : Set (Minkowski d)) ⊆ W ∧
      IsSpacelikeLipschitzIn V {p | p ∈ (V : Set (Minkowski d)) ∧ f p = 0} := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hW p₀ hp₀
  set δ := ρ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hmem : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), |t - p₀.1| ≤ δ → dist x p₀.2 < δ →
      ((t, x) : Minkowski d) ∈ W := by
    intro t x ht hx
    refine hball ?_
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
    exact ⟨by linarith, by linarith⟩
  set U : Set (EuclideanSpace ℝ (Fin d)) := ball p₀.2 δ with hUdef
  have hcle : ∀ y : ℝ, 0 ≤ y → c * y ≤ y := fun y hy => mul_le_of_le_one_left hy hc1.le
  -- existence of a zero on each vertical segment
  have hex : ∀ x ∈ U, ∃ t : ℝ, |t - p₀.1| < δ ∧ f (t, x) = 0 := by
    intro x hx
    have hxd : dist x p₀.2 < δ := hx
    have hxn : ‖x - p₀.2‖ < δ := by rwa [← dist_eq_norm]
    have hcont : ContinuousOn (fun t : ℝ => f (t, x)) (Icc (p₀.1 - δ) (p₀.1 + δ)) := by
      refine hf.comp (continuous_id.prodMk continuous_const).continuousOn ?_
      intro t ht
      exact hmem t x (abs_sub_le_iff.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩) hxd
    have htop : 0 < f (p₀.1 + δ, x) := by
      rw [← hf₀]
      refine hinc p₀ hp₀ _ (hmem _ x (by simp [abs_of_pos hδ]) hxd) ?_
      show c * ‖x - p₀.2‖ < p₀.1 + δ - p₀.1
      linarith [hcle _ (norm_nonneg (x - p₀.2))]
    have hbot : f (p₀.1 - δ, x) < 0 := by
      rw [← hf₀]
      refine hinc _ (hmem _ x (by simp [abs_of_pos hδ]) hxd) p₀ hp₀ ?_
      show c * ‖p₀.2 - x‖ < p₀.1 - (p₀.1 - δ)
      rw [norm_sub_rev]
      linarith [hcle _ (norm_nonneg (x - p₀.2))]
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc (by linarith) hcont ⟨hbot.le, htop.le⟩
    refine ⟨t, abs_sub_lt_iff.2 ⟨?_, ?_⟩, ht0⟩
    · rcases (ht.2).lt_or_eq with h | h
      · linarith
      · exfalso; rw [h] at ht0; exact htop.ne' ht0
    · rcases (ht.1).lt_or_eq with h | h
      · linarith
      · exfalso; rw [← h] at ht0; exact hbot.ne ht0
  choose! F hF using hex
  -- uniqueness on vertical segments
  have huniq : ∀ (t t' : ℝ) (x : EuclideanSpace ℝ (Fin d)), ((t, x) : Minkowski d) ∈ W →
      ((t', x) : Minkowski d) ∈ W → f (t, x) = 0 → f (t', x) = 0 → t = t' := by
    intro t t' x ht ht' h0 h0'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hinc _ ht _ ht' (by simp only [sub_self, norm_zero, mul_zero]; linarith)
      rw [h0, h0'] at this; exact lt_irrefl _ this
    · have := hinc _ ht' _ ht (by simp only [sub_self, norm_zero, mul_zero]; linarith)
      rw [h0, h0'] at this; exact lt_irrefl _ this
  have hFW : ∀ x ∈ U, ((F x, x) : Minkowski d) ∈ W := fun x hx =>
    hmem _ x (hF x hx).1.le hx
  -- the Lipschitz bound
  have hFlip : ∀ x ∈ U, ∀ y ∈ U, F x - F y ≤ c * ‖x - y‖ := by
    intro x hx y hy
    by_contra hlt
    have := hinc _ (hFW y hy) _ (hFW x hx) (not_le.1 hlt)
    rw [(hF y hy).2, (hF x hx).2] at this
    exact lt_irrefl _ this
  have hLip : LipschitzOnWith (⟨c, hc0⟩ : ℝ≥0) F U := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, dist_eq_norm]
    show |F x - F y| ≤ c * ‖x - y‖
    refine abs_sub_le_iff.2 ⟨hFlip x hx y hy, ?_⟩
    rw [norm_sub_rev]; exact hFlip y hy x hx
  -- the ball
  let V : Opens (Minkowski d) := ⟨ball p₀ δ, isOpen_ball⟩
  have hVmem : ∀ p : Minkowski d, p ∈ (V : Set (Minkowski d)) ↔ |p.1 - p₀.1| < δ ∧ p.2 ∈ U := by
    intro p
    show p ∈ ball p₀ δ ↔ _
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
    rfl
  have hVW : (V : Set (Minkowski d)) ⊆ W := by
    intro p hp
    obtain ⟨h1, h2⟩ := (hVmem p).1 hp
    exact hmem p.1 p.2 h1.le h2
  have hzero : ∀ p ∈ (V : Set (Minkowski d)), f p = 0 ↔ p.1 = F p.2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := (hVmem p).1 hp
    constructor
    · intro h0
      exact huniq p.1 (F p.2) p.2 (hVW hp) (hFW _ h2) h0 (hF _ h2).2
    · intro h
      have : p = (F p.2, p.2) := Prod.ext h rfl
      rw [this]; exact (hF _ h2).2
  have hp₀V : p₀ ∈ (V : Set (Minkowski d)) := mem_ball_self hδ
  refine ⟨V, hp₀V, hVW, fun p hp => hp.1, ?_, ?_⟩
  · -- achronal
    rintro p ⟨hpV, hp0⟩ q ⟨hqV, hq0⟩ hpq
    have hlt := minkowski_lt_top_iff.1 ((minkowski d).lt_mono le_top hpq)
    rw [(hzero p hpV).1 hp0, (hzero q hqV).1 hq0] at hlt
    have := hFlip q.2 ((hVmem q).1 hqV).2 p.2 ((hVmem p).1 hpV).2
    linarith [hcle _ (norm_nonneg (q.2 - p.2))]
  · -- the local graph, in the chart's own frame
    intro p hp
    refine ⟨1, V, U, F, ⟨c, hc0⟩, by exact_mod_cast hc1, hp.1, le_rfl, isOpen_ball, hLip, ?_⟩
    rw [one_smul, one_smul]
    ext q
    constructor
    · rintro ⟨⟨hqV, hq0⟩, -⟩
      exact ⟨hqV, ((hVmem q).1 hqV).2, (hzero q hqV).1 hq0⟩
    · rintro ⟨hqV, -, hq⟩
      exact ⟨⟨hqV, (hzero q hqV).2 hq⟩, hqV⟩

/-! ### Zero sets on a charted space -/

section Charted

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]

variable (d) in
/-- **The chart picture of `H` at `x` is locally a cone-increasing zero set**: on an open `W`
around `chartAt x x`, inside the chart's target, it is `{f = 0}` for a continuous
`c`-cone-increasing `f`, `0 ≤ c < 1`. -/
def IsLocallyConeZeroSetAt (H : Set M) (x : M) : Prop :=
  ∃ (W : Set (Minkowski d)) (f : Minkowski d → ℝ) (c : ℝ), 0 ≤ c ∧ c < 1 ∧
    IsOpen W ∧ chartAt (Minkowski d) x x ∈ W ∧ W ⊆ (chartAt (Minkowski d) x).target ∧
    ContinuousOn f W ∧ IsConeIncreasingOn c f W ∧
    ∀ p ∈ W, (p ∈ chartAt (Minkowski d) x '' (H ∩ (chartAt (Minkowski d) x).source) ↔ f p = 0)

/-- **The local criterion**: if the chart picture of `H` at each of its points is locally a
cone-increasing zero set, then `H` is spacelike Lipschitz (`exists_isSpacelikeLipschitzIn_zeroSet`
in the chart at `x`). -/
theorem isSpacelikeLipschitz_of_locally_coneIncreasing {H : Set M}
    (h : ∀ x ∈ H, IsLocallyConeZeroSetAt d H x) : IsSpacelikeLipschitz d H := by
  intro x hx
  obtain ⟨W, f, c, hc0, hc1, hWo, hxW, hWt, hfc, hinc, hiff⟩ := h x hx
  have hf0 : f (chartAt (Minkowski d) x x) = 0 :=
    (hiff _ hxW).1 ⟨x, ⟨hx, mem_chart_source _ x⟩, rfl⟩
  obtain ⟨V, hpV, hVW, hV⟩ := exists_isSpacelikeLipschitzIn_zeroSet hWo hfc hc0 hc1 hinc hxW hf0
  refine ⟨V, hpV, hVW.trans hWt, ?_⟩
  have heq : chartAt (Minkowski d) x '' (H ∩ (chartAt (Minkowski d) x).source) ∩
      (V : Set (Minkowski d)) = {p | p ∈ (V : Set (Minkowski d)) ∧ f p = 0} := by
    ext p
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (hiff p (hVW h2)).1 h1⟩
    · rintro ⟨h2, h3⟩; exact ⟨(hiff p (hVW h2)).2 h3, h2⟩
  rw [heq]; exact hV

/-- **A future envelope of hyperboloids is locally a cone-increasing zero set**: if near
`chartAt x x` the chart picture of `H` is `{max_{(q, k) ∈ s} (sqTimeSep q · − k) = 0}` for a
finite nonempty `s` whose centres `q` are all chronologically before `chartAt x x` (the level set
`sup_y τ(y, ·) = ε` of a local time separation from a finite set), then
`IsLocallyConeZeroSetAt d H x`. -/
theorem isLocallyConeZeroSetAt_of_sup'_sqTimeSep {H : Set M} {x : M}
    {W : Set (Minkowski d)} {s : Finset (Minkowski d × ℝ)} (hs : s.Nonempty) (hWo : IsOpen W)
    (hxW : chartAt (Minkowski d) x x ∈ W) (hWt : W ⊆ (chartAt (Minkowski d) x).target)
    (hlt : ∀ i ∈ s, (minkowski d).lt ⊤ i.1 (chartAt (Minkowski d) x x))
    (hiff : ∀ p ∈ W, (p ∈ chartAt (Minkowski d) x '' (H ∩ (chartAt (Minkowski d) x).source) ↔
        (s.sup' hs fun i => sqTimeSep i.1 p - i.2) = 0)) :
    IsLocallyConeZeroSetAt d H x := by
  obtain ⟨c, hc0, hc1, W', hW'o, hxW', hsup, -⟩ := exists_isConeIncreasingOn_sup'_inf' s hs
    Prod.fst Prod.snd (p₀ := chartAt (Minkowski d) x x)
    fun i hi => minkowski_lt_top_iff.1 (hlt i hi)
  refine ⟨W ∩ W', _, c, hc0, hc1, hWo.inter hW'o, ⟨hxW, hxW'⟩, inter_subset_left.trans hWt,
    ?_, hsup.mono le_rfl inter_subset_right, fun p hp => hiff p hp.1⟩
  exact ContinuousOn.finset_sup'_apply hs fun i _ =>
    ((continuous_sqTimeSep i.1).sub continuous_const).continuousOn

/-- **The upper boundary of a union of pasts of hyperboloid caps is locally a cone-increasing
zero set**: as `isLocallyConeZeroSetAt_of_sup'_sqTimeSep`, with a finite `min` (near a point of
`K ∖ I⁻(K)` interior to the caps `Cₖ = {sqTimeSep qₖ · = εₖ²}` through it, the chart picture is
`{min_k (sqTimeSep qₖ · − εₖ²) = 0}`). -/
theorem isLocallyConeZeroSetAt_of_inf'_sqTimeSep {H : Set M} {x : M}
    {W : Set (Minkowski d)} {s : Finset (Minkowski d × ℝ)} (hs : s.Nonempty) (hWo : IsOpen W)
    (hxW : chartAt (Minkowski d) x x ∈ W) (hWt : W ⊆ (chartAt (Minkowski d) x).target)
    (hlt : ∀ i ∈ s, (minkowski d).lt ⊤ i.1 (chartAt (Minkowski d) x x))
    (hiff : ∀ p ∈ W, (p ∈ chartAt (Minkowski d) x '' (H ∩ (chartAt (Minkowski d) x).source) ↔
        (s.inf' hs fun i => sqTimeSep i.1 p - i.2) = 0)) :
    IsLocallyConeZeroSetAt d H x := by
  obtain ⟨c, hc0, hc1, W', hW'o, hxW', -, hinf⟩ := exists_isConeIncreasingOn_sup'_inf' s hs
    Prod.fst Prod.snd (p₀ := chartAt (Minkowski d) x x)
    fun i hi => minkowski_lt_top_iff.1 (hlt i hi)
  refine ⟨W ∩ W', _, c, hc0, hc1, hWo.inter hW'o, ⟨hxW, hxW'⟩, inter_subset_left.trans hWt,
    ?_, hinf.mono le_rfl inter_subset_right, fun p hp => hiff p hp.1⟩
  exact ContinuousOn.finset_inf'_apply hs fun i _ =>
    ((continuous_sqTimeSep i.1).sub continuous_const).continuousOn

end Charted

/-! ### The upper part `K ∖ I⁻(K)` of a compact set -/

section Upper

variable {M : Type*} [TopologicalSpace M]

/-- **The upper part of a compact set is compact**: `I⁻(K)` is open. -/
theorem isCompact_diff_Iminus (C : Causality M) {K : Set M} (hK : IsCompact K) :
    IsCompact (K \ C.Iminus ⊤ K) :=
  hK.diff C.isOpen_Iminus

/-- **A nonempty compact set of a chronological spacetime has a point not in its chronological
past.** Otherwise finitely many `I⁻(kᵢ)`, `kᵢ ∈ K`, cover `K`; every `kᵢ` lies below some `kⱼ`,
so iterating gives a chronological chain in a finite set, which closes up: `k ≪ k`. -/
theorem nonempty_diff_Iminus (C : Causality M) (hchr : ∀ x, ¬ C.lt ⊤ x x) {K : Set M}
    (hK : IsCompact K) (hne : K.Nonempty) : (K \ C.Iminus ⊤ K).Nonempty := by
  by_contra hcon
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hcon
  have hcov : K ⊆ ⋃ k ∈ K, {y | C.lt ⊤ y k} := fun y hy => by
    obtain ⟨k, hk, hyk⟩ := hcon hy
    exact mem_biUnion hk hyk
  obtain ⟨t, htK, htf, htcov⟩ :=
    hK.elim_finite_subcover_image (fun k _ => C.isOpen_lt_left ⊤ k) hcov
  have hnext : ∀ x ∈ t, ∃ y ∈ t, C.lt ⊤ x y := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (htcov (htK hx))
    exact ⟨y, hy, hxy⟩
  choose! g hgt hg using hnext
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨y₀, hy₀, -⟩ := mem_iUnion₂.1 (htcov hx₀)
  have hmem : ∀ n : ℕ, g^[n] y₀ ∈ t := by
    intro n
    induction n with
    | zero => exact hy₀
    | succ n ih => rw [Function.iterate_succ_apply']; exact hgt _ ih
  have hchain : ∀ m n : ℕ, m < n → C.lt ⊤ (g^[m] y₀) (g^[n] y₀) := by
    intro m n hmn
    induction n with
    | zero => exact absurd hmn (Nat.not_lt_zero _)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
      · exact C.lt_trans (ih h) (hg _ (hmem n))
      · rw [h]; exact hg _ (hmem n)
  obtain ⟨m, n, hmn, heq⟩ := htf.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ => g^[n] y₀) hmem
  have := hchain m n hmn
  rw [heq] at this
  exact hchr _ this

end Upper

end Causal.Flat.Cla
