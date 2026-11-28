import Causal.GHWithoutTarentin
import Causal.PastInextensibleMeetsCauchy
import Causal.LineDevelopment
import Causal.CauchyExtension

/-!
# Sbierski's (2.4) needs `≤` antisymmetric: a ray glued to a circle

Programme target `T-abs-meets-cauchy-antisymmetry-sharp` (`programme/roadmap.toml`; layer 1: it
imports `Causal.GHWithoutTarentin`, `Causal.PastInextensibleMeetsCauchy`, `Causal.LineDevelopment`
and `Causal.CauchyExtension`, all ETT-layer; no model; no metric notion in a statement). There is
no statement of `ETT.tex` behind it, so **no label is marked**. It shows that the antisymmetry
hypothesis `hcaus` of `Causal.Causality.PastInextensible.exists_mem_of_mem_Jplus`
(`Causal/PastInextensibleMeetsCauchy.lean:147`), Sbierski 2312.07443's (2.4), cannot be dropped.

> X ⊆ ℝ² is the unit circle with the ray {(1 + r, 0) : r ≥ 0} attached at q = (1, 0), with
> Causal.arcCausality of arcs running inward along the ray and counterclockwise round the circle
> (≪ empty). One conjoined theorem: X is T2 and second countable; the causality is causally
> arc-connected and absolutely minimal on every open set; ≤ is not antisymmetric (q ≤ y ≤ q for
> y = (−1, 0)); {y} is a Cauchy surface of X; and a past-inextensible causal curve along the ray
> has the point q ∈ J⁺({y}) and misses y. So PastInextensible.exists_mem_of_mem_Jplus fails
> without its antisymmetry hypothesis (the target's title, `programme/roadmap.toml`)

## What is proved (no `sorry`)

1. **The witness** (`rayCircle_separates_pastInextensible_meets`): every conjunct of the target,
   with `≪` empty, plain absolute minimality, `q ≤ y`, `y ≤ q`, `q ≠ y` and `σ 0 = q` stated as
   well. Its bare form (`not_pastInextensible_exists_mem_of_mem_Jplus_bare`): over Hausdorff,
   second countable spaces, (2.4) without antisymmetry is false.
2. **`{y}` is a Cauchy surface** (`rayCircle_isCauchySurface_Y`), through
   `rayCircle_extensible_of_forall_ne`: a causal curve missing `y` is extensible. Off `y`, the angle
   from `q` (`rayCircleAngle`: `1 - x` on the ray, the argument on the circle, the evidence's
   signed arc length `τ`) does not decrease along `≤_U` (`rayCircleAngle_le_of_le`). The curve
   cannot meet both the open ray and the open lower half-circle: both have negative angle, and
   they are disjoint and open. So the curve is `Γ ∘ (angle ∘ c)` for one of two standard causal
   curves `Γ`, both reaching `y` at angle `π`: `rayCircleCurveRay` over `]-∞, π]` (the ray, then
   the upper half) and `rayCircleCurveLow` over `[-π, π]` (the lower half, then the upper half).
3. **The ray** (`rayCircleRay`: inward along the ray for `t ≤ 0`, at rest at `q` for `t ≥ 0`), a
   causal curve over `ℝ`: past-inextensible (no limit at `-∞`,
   `LineDevelopment.pastInextensible_of_not_tendsto_atBot`), `q ∈ J⁺({y})` along the lower half,
   missing `y`.
4. **Three model-free lemmas** (`Causal.Causality`, no hypothesis on the causality or the space):
   `extensible_of_graph` (if `c = γ ∘ h` on `I`, with `h` continuous and non-decreasing and `γ` a
   causal curve over `J`, and `γ` has a parameter `t' ≥ h '' I` with a value `c` does not take,
   then `c` is extensible); `causalCurveIn_top_of_pieces` (a continuous map with `γ s ≤_N γ s'`
   whenever `γ '' [s, s'] ⊆ N` is a causal curve of `M`); `CausalCurveIn.continuousOn_interval`.

## Hypothesis checklist

| `PastInextensible.exists_mem_of_mem_Jplus_of_isCausal` (`:191`) | here |
|---|---|
| `[T1Space M]` | ✓ stronger: T2 (a subspace of `ℝ × ℝ`, mathlib instance) |
| `[SecondCountableTopology M]` | ✓ (mathlib instance) |
| `S` a Cauchy surface of `M` (DEC-14) | ✓ `S = {y}` (`rayCircle_isCauchySurface_Y`) |
| `C.CausallyArcConnected` | ✓ (`arcCausality_causallyArcConnected`); absolutely minimal too |
| `C.IsCausal` (`≤` antisymmetric) | ✗ the hypothesis dropped: `q ≤ y ≤ q`, `q ≠ y` |
| `σ` past-inextensible (DEC-13) | ✓ the ray over `ℝ` |
| a point of `σ` in `J⁺(S)` | ✓ `σ 0 = q` and `y ≤ q` |
| conclusion: `σ` meets `S` | ✗ fails: `σ` misses `y` |

## SCOPE (disclosed)

* **Nothing marked**: no label of `ETT.tex`, and no binder exists for 2312.07443.
* **The model as the target words it**: the unit circle and the ray, `q = (1, 0)`, `y = (-1, 0)`.
  Arcs over `[0, 1]`: the upper half-circle `s ↦ (cos πs, sin πs)` from `q` to `y`, the lower one
  `s ↦ (-cos πs, -sin πs)` from `y` to `q`, and for each `n : ℕ` the ray piece
  `s ↦ (1 + n(1 - s), 0)` from `(1 + n, 0)` to `q` (`max (1 - s) 0` keeps it in `X` off `[0, 1]`).
  The arcs are not `ArcCoherent` (else `ArcCoherent.isCausal`): `≤` is the chain closure.
* **The evidence's argument, with the extension step changed.** Its `τ` and its monotonicity off `y`
  are as argued. Its case analysis at the future end ("eventually constant, or converges to a point
  of `X`") is not made. The curve lies on a standard curve at its angle, and `extensible_of_graph`
  extends it along that curve up to `y` itself, so the new value is always `y`; the parameter is
  first compressed by `arctan`. No limit of the curve is taken, only the supremum of its angle.
  SubArc's end-piece lemmas are not needed, only its `CausalCurveIn.comp_monotoneOn`; the
  library's `extensible_of_tendsto` (which asks `StronglyCausal`) is not used.
* `extensible_of_graph` generalises `Causality.extensible_of_timeGraph_openEnd`
  (`Causal/Remarks/SingularRowsCauchyExt.lean:230`, model layer through
  `Causal.Port.CupCapBTZCounterexample`, so not importable here): no time function, no open end,
  any interval. `CausalCurveIn.continuousOn_interval` is the ETT-layer twin of that module's
  `continuousOn_of_causalCurveIn` (`:203`); the names differ.
* Trigonometry, `Complex.arg` and the complex norm appear in the definitions, the proofs and four
  helper statements about the circle's parametrisation and its angle (`rayCircle_arg_cos_add_sin`,
  `rayCircleAngle_of_circle`, `rayCircleCurveLow_arg`, `rayCircleC_norm_of_circle`); none appears
  in the witness, the bare form or the model-free lemmas.
* Not proved (not asked): the time-reversed witness; the finding's second model (for causal
  arc-connectedness), which the target's evidence does not take.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Function TopologicalSpace Topology Filter Real

/-! ## 1. Three model-free lemmas on curves -/

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M}

/-- A causal curve over an interval is continuous on it. -/
theorem CausalCurveIn.continuousOn_interval {W : Opens M} {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) : ContinuousOn c I := by
  intro s hs
  by_cases hleft : ∃ j ∈ I, j < s
  · obtain ⟨j, hj, hjs⟩ := hleft
    by_cases hright : ∃ i ∈ I, s < i
    · obtain ⟨i, hi, hsi⟩ := hright
      have hmem : Icc j i ∈ 𝓝[I] s := nhdsWithin_le_nhds (Icc_mem_nhds hjs hsi)
      exact ((hc.continuousOn_Icc hj hi) s ⟨hjs.le, hsi.le⟩).mono_of_mem_nhdsWithin hmem
    · push Not at hright
      have hmem : Icc j s ∈ 𝓝[I] s :=
        mem_nhdsWithin.2 ⟨Ioi j, isOpen_Ioi, hjs, fun x hx => ⟨hx.1.le, hright x hx.2⟩⟩
      exact ((hc.continuousOn_Icc hj hs) s ⟨hjs.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem
  · push Not at hleft
    by_cases hright : ∃ i ∈ I, s < i
    · obtain ⟨i, hi, hsi⟩ := hright
      have hmem : Icc s i ∈ 𝓝[I] s :=
        mem_nhdsWithin.2 ⟨Iio i, isOpen_Iio, hsi, fun x hx => ⟨hleft x hx.2, hx.1.le⟩⟩
      exact ((hc.continuousOn_Icc hs hi) s ⟨le_rfl, hsi.le⟩).mono_of_mem_nhdsWithin hmem
    · push Not at hright
      have hI : I ⊆ {s} := fun x hx => le_antisymm (hright x hx) (hleft x hx)
      exact (continuousWithinAt_singleton (f := c) (x := s)).mono hI

/-- **A continuous map whose pieces are related is a causal curve**: if `γ` is continuous and
`γ s ≤_N γ s'` whenever `s ≤ s'` in `J` and `γ` maps `[s, s']` into the open set `N`, then `γ` is a
causal curve of `M` over `J`. -/
theorem causalCurveIn_top_of_pieces {γ : ℝ → M} {J : Set ℝ} (hγ : Continuous γ)
    (hne : J.Nonempty) (hoc : J.OrdConnected)
    (hpiece : ∀ s ∈ J, ∀ s' ∈ J, s ≤ s' → ∀ N : Opens M, γ '' Icc s s' ⊆ N →
      C.le N (γ s) (γ s')) :
    C.CausalCurveIn ⊤ J γ := by
  refine ⟨hne, hoc, fun a ha b hb => ⟨fun _ _ => trivial, fun t _ N _ htN => ?_⟩⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (N.isOpen.preimage hγ) t htN
  refine ⟨t - δ, t + δ, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 => ?_⟩
  refine hpiece s (hoc.out ha hb hs) s' (hoc.out ha hb hs') h2.le N ?_
  rintro _ ⟨r, hr, rfl⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hr.1, hr.2]

/-- **Extension along a graph, bounded case**: `extensible_of_graph` for `I` bounded above. The new
curve is `γ ∘ g` over `I ∪ [b, b + (t' - k)]`, `b = sup I`, `k = sup h(I)`, with `g = h` below `b`
and `g = k + (· - b)` from `b` on; its value at `b + (t' - k)` is `γ t'`. -/
theorem extensible_of_graph_of_bddAbove {W : Opens M} {I J : Set ℝ} {c γ : ℝ → M} {h : ℝ → ℝ}
    {t' : ℝ} (hγ : C.CausalCurveIn W J γ) (hc : C.CausalCurveIn W I c) (hbdd : BddAbove I)
    (hmono : MonotoneOn h I) (hcont : ContinuousOn h I) (hJ : MapsTo h I J)
    (heq : ∀ t ∈ I, γ (h t) = c t) (ht' : t' ∈ J) (hle : ∀ t ∈ I, h t ≤ t')
    (hnew : ∀ t ∈ I, γ t' ≠ c t) : C.Extensible W I c := by
  obtain ⟨t₀, ht₀⟩ := hc.nonempty
  set b := sSup I with hb
  have hbI : ∀ t ∈ I, t ≤ b := fun t ht => le_csSup hbdd ht
  have hhne : (h '' I).Nonempty := hc.nonempty.image h
  have hhbdd : BddAbove (h '' I) := ⟨t', by rintro _ ⟨t, ht, rfl⟩; exact hle t ht⟩
  set k := sSup (h '' I) with hk
  have hhk : ∀ t ∈ I, h t ≤ k := fun t ht => le_csSup hhbdd ⟨t, ht, rfl⟩
  have hkt' : k ≤ t' := csSup_le hhne (by rintro _ ⟨t, ht, rfl⟩; exact hle t ht)
  have hbk : b ∈ I → h b = k := fun hb' => le_antisymm (hhk b hb')
    (csSup_le hhne (by rintro _ ⟨t, ht, rfl⟩; exact hmono ht hb' (hbI t ht)))
  set L := t' - k with hL
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  set I' : Set ℝ := I ∪ Icc b (b + L) with hI'
  set g : ℝ → ℝ := fun s => if s < b then h s else k + (s - b) with hg
  have hglt : ∀ s, s < b → g s = h s := fun s hs => if_pos hs
  have hgge : ∀ s, b ≤ s → g s = k + (s - b) := fun s hs => if_neg (not_lt.2 hs)
  have hgI : ∀ t ∈ I, g t = h t := by
    intro t ht
    rcases (hbI t ht).lt_or_eq with h1 | h1
    · exact hglt t h1
    · rw [hgge t h1.ge, h1, sub_self, add_zero, hbk (h1 ▸ ht)]
  have hlowI : ∀ s ∈ I', s < b → s ∈ I := by
    rintro s (hs | hs) hsb
    · exact hs
    · exact absurd hs.1 (not_le.2 hsb)
  have hoc : I'.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    rcases lt_or_ge z b with hzb | hzb
    · have hxI : x ∈ I := hlowI x hx (hz.1.trans_lt hzb)
      obtain ⟨i, hi, hzi⟩ := exists_lt_of_lt_csSup ⟨t₀, ht₀⟩ hzb
      exact Or.inl (hc.ordConnected.out hxI hi ⟨hz.1, hzi.le⟩)
    · refine Or.inr ⟨hzb, hz.2.trans ?_⟩
      rcases hy with hy | hy
      · linarith [hbI y hy]
      · exact hy.2
  have hmaps : MapsTo g I' J := by
    intro s hs
    rcases lt_or_ge s b with hsb | hsb
    · rw [hglt s hsb]; exact hJ (hlowI s hs hsb)
    · rw [hgge s hsb]
      have hsL : s ≤ b + L := by
        rcases hs with hs | hs
        · linarith [hbI s hs]
        · exact hs.2
      exact hγ.ordConnected.out (hJ ht₀) ht' ⟨by linarith [hhk t₀ ht₀], by linarith⟩
  have hgmono : MonotoneOn g I' := by
    intro x hx y hy hxy
    rcases lt_or_ge y b with hyb | hyb
    · have hxb : x < b := hxy.trans_lt hyb
      rw [hglt x hxb, hglt y hyb]
      exact hmono (hlowI x hx hxb) (hlowI y hy hyb) hxy
    · rw [hgge y hyb]
      rcases lt_or_ge x b with hxb | hxb
      · rw [hglt x hxb]; linarith [hhk x (hlowI x hx hxb)]
      · rw [hgge x hxb]; linarith
  have hgcont : ContinuousOn g I' := by
    intro s hs
    rcases lt_trichotomy s b with hsb | hsb | hsb
    · have hsI : s ∈ I := hlowI s hs hsb
      have hmem : I ∈ 𝓝[I'] s := mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, hsb,
        fun x hx => hlowI x hx.2 hx.1⟩
      exact ((hcont s hsI).congr (fun x hx => hgI x hx) (hgI s hsI)).mono_of_mem_nhdsWithin hmem
    · rw [hsb]
      have hgb : g b = k := by rw [hgge b le_rfl, sub_self, add_zero]
      have hsub : I' ⊆ (I ∩ Iio b) ∪ Icc b (b + L) := by
        rintro x (hx | hx)
        · rcases (hbI x hx).lt_or_eq with h1 | h1
          · exact Or.inl ⟨hx, h1⟩
          · exact Or.inr ⟨h1.ge, by linarith⟩
        · exact Or.inr hx
      refine ContinuousWithinAt.mono (ContinuousWithinAt.union ?_ ?_) hsub
      · rw [ContinuousWithinAt, hgb]
        have htend : Tendsto h (𝓝[I ∩ Iio b] b) (𝓝 k) := by
          by_cases hbI' : b ∈ I
          · have := hcont b hbI'
            rw [ContinuousWithinAt, hbk hbI'] at this
            exact this.mono_left (nhdsWithin_mono _ inter_subset_left)
          · rw [Metric.tendsto_nhdsWithin_nhds]
            intro ε hε
            obtain ⟨_, ⟨i, hi, rfl⟩, hki⟩ := exists_lt_of_lt_csSup hhne
              (show k - ε < k by linarith)
            have hib : i < b := lt_of_le_of_ne (hbI i hi) (fun he => hbI' (he ▸ hi))
            refine ⟨b - i, by linarith, fun x hx hxd => ?_⟩
            rw [Real.dist_eq, abs_lt] at hxd
            have hix : i ≤ x := by linarith [hxd.1, hx.2]
            have := hmono hi hx.1 hix
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hhk x hx.1]
        exact htend.congr' (eventually_nhdsWithin_of_forall fun x hx => (hglt x hx.2).symm)
      · have hcA : ContinuousOn (fun s => k + (s - b)) (Icc b (b + L)) := by fun_prop
        exact (hcA b ⟨le_rfl, by linarith⟩).congr (fun x hx => hgge x hx.1) (hgge b le_rfl)
    · have h1 : ContinuousWithinAt (fun s => k + (s - b)) I' s :=
        (by fun_prop : Continuous (fun s : ℝ => k + (s - b))).continuousWithinAt
      refine h1.congr_of_eventuallyEq ?_ (hgge s hsb.le)
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hsb)] with x hx
      exact hgge x (show b < x from hx).le
  have hcurve : C.CausalCurveIn W I' (γ ∘ g) :=
    hγ.comp_monotoneOn ⟨t₀, Or.inl ht₀⟩ hoc hgmono hgcont hmaps
  refine ⟨I', γ ∘ g, hcurve, ⟨id, strictMonoOn_id, fun t ht => Or.inl ht,
    by rw [image_id]; exact hc.ordConnected, fun t ht => ?_⟩,
    ⟨b + L, Or.inr ⟨by linarith, le_rfl⟩, fun t ht => ?_⟩⟩
  · show γ (g t) = c t
    rw [hgI t ht]; exact heq t ht
  · show γ (g (b + L)) ≠ c t
    have : g (b + L) = t' := by rw [hgge (b + L) (by linarith), hL]; ring
    rw [this]; exact hnew t ht

/-- **A causal curve lying on a causal curve `γ` that goes on to a new value is extensible**: if
`c = γ ∘ h` on `I`, with `h` continuous and non-decreasing, and `γ` has a parameter `t'` above
`h '' I` with a value `c` does not take, then `c` is extensible. No hypothesis on the causality:
the new curve is `γ` read through `h`, then through an affine piece up to `t'` (after a
compression of `I` by `arctan`). -/
theorem extensible_of_graph {W : Opens M} {I J : Set ℝ} {c γ : ℝ → M} {h : ℝ → ℝ} {t' : ℝ}
    (hγ : C.CausalCurveIn W J γ) (hc : C.CausalCurveIn W I c)
    (hmono : MonotoneOn h I) (hcont : ContinuousOn h I) (hJ : MapsTo h I J)
    (heq : ∀ t ∈ I, γ (h t) = c t) (ht' : t' ∈ J) (hle : ∀ t ∈ I, h t ≤ t')
    (hnew : ∀ t ∈ I, γ t' ≠ c t) : C.Extensible W I c := by
  have htan : ∀ t, Real.tan (Real.arctan t) = t := Real.tan_arctan
  set I₁ := Real.arctan '' I with hI₁
  have hsub : I₁ ⊆ Ioo (-(π / 2)) (π / 2) := by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨Real.neg_pi_div_two_lt_arctan t, Real.arctan_lt_pi_div_two t⟩
  have hmaps : MapsTo Real.tan I₁ I := by
    rintro _ ⟨t, ht, rfl⟩; rw [htan]; exact ht
  have hdc : C.CausalCurveIn W I₁ (c ∘ Real.tan) :=
    hc.comp (hc.nonempty.image _)
      (isPreconnected_iff_ordConnected.1
        (hc.ordConnected.isPreconnected.image _ Real.continuous_arctan.continuousOn))
      (Real.strictMonoOn_tan.mono hsub) (Real.continuousOn_tan_Ioo.mono hsub) hmaps
  have hext : C.Extensible W I₁ (c ∘ Real.tan) := by
    refine extensible_of_graph_of_bddAbove (h := h ∘ Real.tan) hγ hdc
      ⟨π / 2, fun x hx => (hsub hx).2.le⟩ ?_
      (hcont.comp (Real.continuousOn_tan_Ioo.mono hsub) hmaps) (hJ.comp hmaps) ?_ ht' ?_ ?_
    · intro x hx y hy hxy
      exact hmono (hmaps hx) (hmaps hy) ((Real.strictMonoOn_tan.mono hsub).monotoneOn hx hy hxy)
    · intro s hs; exact heq _ (hmaps hs)
    · intro s hs; exact hle _ (hmaps hs)
    · intro s hs; exact hnew _ (hmaps hs)
  exact hext.of_comp (ψ := Real.arctan) (Real.arctan_strictMono.strictMonoOn _)
    (mapsTo_image _ _) (surjOn_image _ _) fun t _ => by simp only [Function.comp, htan]

end Causality

/-! ## 2. The carrier, the arcs, the causality -/

/-- **The ray glued to the circle**, a subspace of `ℝ²`: the unit circle, and the ray
`{(1 + r, 0) : r ≥ 0}` attached to it at `q = (1, 0)`. -/
def rayCircleSet : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 = 1} ∪ {p | 1 ≤ p.1 ∧ p.2 = 0}

/-- The arcs of the ray glued to the circle: the upper half-circle from `q` to `y = (-1, 0)`, the
lower half-circle from `y` to `q` (both counterclockwise), and for each `n` the piece of the ray
from `(1 + n, 0)` inward to `q`. -/
inductive RayCircleArc
  | up
  | low
  | ray (n : ℕ)

/-- The arcs, as maps into `ℝ²`. -/
noncomputable def rayCircleArc : RayCircleArc → ℝ → ℝ × ℝ
  | .up, s => (cos (π * s), sin (π * s))
  | .low, s => (-cos (π * s), -sin (π * s))
  | .ray n, s => (1 + n * max (1 - s) 0, 0)

theorem rayCircleArc_mem (i : RayCircleArc) (s : ℝ) : rayCircleArc i s ∈ rayCircleSet := by
  cases i with
  | up => exact Or.inl (cos_sq_add_sin_sq _)
  | low =>
    refine Or.inl ?_
    show (-cos (π * s)) ^ 2 + (-sin (π * s)) ^ 2 = 1
    rw [neg_sq, neg_sq, cos_sq_add_sin_sq]
  | ray n =>
    exact Or.inr ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (le_max_right _ _)), rfl⟩

/-- The arcs, as maps into the ray glued to the circle. -/
noncomputable def rayCircleγ (i : RayCircleArc) (s : ℝ) : rayCircleSet :=
  ⟨rayCircleArc i s, rayCircleArc_mem i s⟩

/-- **The causality of the ray glued to the circle**: `≤_U` along the arcs inside `U` (inward
along the ray, counterclockwise round the circle), `≪` empty. -/
noncomputable def rayCircle : Causality rayCircleSet := arcCausality rayCircleγ

/-- The junction `q = (1, 0)`. -/
def rayCircleQ : rayCircleSet := ⟨(1, 0), Or.inr ⟨le_rfl, rfl⟩⟩

/-- The point `y = (-1, 0)`, opposite `q` on the circle. -/
def rayCircleY : rayCircleSet := ⟨(-1, 0), Or.inl (by norm_num)⟩

theorem continuous_rayCircleγ (i : RayCircleArc) : Continuous (rayCircleγ i) := by
  refine Continuous.subtype_mk ?_ _
  cases i with
  | up => exact (by fun_prop : Continuous fun s : ℝ => (cos (π * s), sin (π * s)))
  | low => exact (by fun_prop : Continuous fun s : ℝ => (-cos (π * s), -sin (π * s)))
  | ray n => exact (by fun_prop : Continuous fun s : ℝ => (1 + (n : ℝ) * max (1 - s) 0, (0 : ℝ)))

theorem rayCircle_causallyArcConnected : rayCircle.CausallyArcConnected :=
  arcCausality_causallyArcConnected continuous_rayCircleγ

theorem rayCircle_absolutelyMinimal : rayCircle.AbsolutelyMinimal :=
  arcCausality_absolutelyMinimal continuous_rayCircleγ

theorem rayCircle_absolutelyMinimalOn (W : Opens rayCircleSet) :
    rayCircle.AbsolutelyMinimalOn W :=
  arcCausality_absolutelyMinimalOn continuous_rayCircleγ W

/-! ## 3. The loop: `q ≤ y ≤ q` -/

theorem rayCircleQ_ne_Y : rayCircleQ ≠ rayCircleY := by
  intro h
  have := congrArg (fun p : rayCircleSet => p.1.1) h
  norm_num [rayCircleQ, rayCircleY] at this

theorem rayCircleγ_up_zero : rayCircleγ .up 0 = rayCircleQ := by
  apply Subtype.ext; simp [rayCircleγ, rayCircleArc, rayCircleQ]

theorem rayCircleγ_up_one : rayCircleγ .up 1 = rayCircleY := by
  apply Subtype.ext; simp [rayCircleγ, rayCircleArc, rayCircleY]

theorem rayCircleγ_low_zero : rayCircleγ .low 0 = rayCircleY := by
  apply Subtype.ext; simp [rayCircleγ, rayCircleArc, rayCircleY]

theorem rayCircleγ_low_one : rayCircleγ .low 1 = rayCircleQ := by
  apply Subtype.ext; simp [rayCircleγ, rayCircleArc, rayCircleQ]

/-- `q ≤ y`, along the upper half-circle. -/
theorem rayCircle_le_Q_Y : rayCircle.le ⊤ rayCircleQ rayCircleY := by
  have h := arcCausality_le_arc (γ := rayCircleγ) RayCircleArc.up (le_refl (0 : ℝ)) zero_le_one
    le_rfl
  rwa [rayCircleγ_up_zero, rayCircleγ_up_one] at h

/-- `y ≤ q`, along the lower half-circle. -/
theorem rayCircle_le_Y_Q : rayCircle.le ⊤ rayCircleY rayCircleQ := by
  have h := arcCausality_le_arc (γ := rayCircleγ) RayCircleArc.low (le_refl (0 : ℝ)) zero_le_one
    le_rfl
  rwa [rayCircleγ_low_zero, rayCircleγ_low_one] at h

/-- **`≤` is not antisymmetric** (`is_causal` fails): `q ≤ y ≤ q` round the circle. -/
theorem rayCircle_not_isCausal : ¬ rayCircle.IsCausal := fun h =>
  rayCircleQ_ne_Y (h rayCircle_le_Q_Y rayCircle_le_Y_Q)

/-! ## 4. The angle from `q`, non-decreasing along the arcs off `y` -/

/-- The point of `ℂ` with the coordinates of `p`. -/
noncomputable def rayCircleC (p : rayCircleSet) : ℂ := (p.1.1 : ℂ) + (p.1.2 : ℂ) * Complex.I

theorem rayCircleC_re (p : rayCircleSet) : (rayCircleC p).re = p.1.1 := by
  simp [rayCircleC]

theorem rayCircleC_im (p : rayCircleSet) : (rayCircleC p).im = p.1.2 := by
  simp [rayCircleC]

theorem continuous_rayCircleC : Continuous rayCircleC := by
  unfold rayCircleC; fun_prop

theorem rayCircle_arg_cos_add_sin {x : ℝ} (hx : x ∈ Ioc (-π) π) :
    Complex.arg ((cos x : ℂ) + (sin x : ℂ) * Complex.I) = x := by
  rw [Complex.ofReal_cos, Complex.ofReal_sin]; exact Complex.arg_cos_add_sin_mul_I hx

/-- **The angle from `q`**: `1 - x ≤ 0` on the ray, the argument in `]-π, π]` on the circle
(`π` at `y`). -/
noncomputable def rayCircleAngle (p : rayCircleSet) : ℝ :=
  Complex.arg (rayCircleC p) + min 0 (1 - p.1.1)

theorem rayCircleAngle_up {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    rayCircleAngle (rayCircleγ .up s) = π * s := by
  have hC : rayCircleC (rayCircleγ .up s) = (cos (π * s) : ℂ) + (sin (π * s) : ℂ) * Complex.I :=
    rfl
  have hu : (rayCircleγ .up s).1.1 = cos (π * s) := rfl
  unfold rayCircleAngle
  rw [hC, rayCircle_arg_cos_add_sin ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩,
    hu, min_eq_left (sub_nonneg.2 (cos_le_one _)), add_zero]

theorem rayCircleAngle_low {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    rayCircleAngle (rayCircleγ .low s) = π * s - π := by
  have hC : rayCircleC (rayCircleγ .low s) =
      (cos (π * s - π) : ℂ) + (sin (π * s - π) : ℂ) * Complex.I := by
    rw [cos_sub_pi, sin_sub_pi]; rfl
  have hu : (rayCircleγ .low s).1.1 = -cos (π * s) := rfl
  unfold rayCircleAngle
  rw [hC, rayCircle_arg_cos_add_sin ⟨by nlinarith [pi_pos, hs.1], by nlinarith [pi_pos, hs.2]⟩,
    hu, min_eq_left (by linarith [neg_one_le_cos (π * s)]), add_zero]

theorem rayCircleAngle_ray (n : ℕ) {s : ℝ} (hs : s ≤ 1) :
    rayCircleAngle (rayCircleγ (.ray n) s) = -(n * (1 - s)) := by
  have hmax : max (1 - s) 0 = 1 - s := max_eq_left (by linarith)
  have hn : 0 ≤ (n : ℝ) * (1 - s) := mul_nonneg (Nat.cast_nonneg n) (by linarith)
  have hC : rayCircleC (rayCircleγ (.ray n) s) = ((1 + n * (1 - s) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [rayCircleC_re, rayCircleC_im, rayCircleγ, rayCircleArc, hmax]
  have hu : (rayCircleγ (.ray n) s).1.1 = 1 + n * (1 - s) := by
    simp [rayCircleγ, rayCircleArc, hmax]
  unfold rayCircleAngle
  rw [hC, Complex.arg_ofReal_of_nonneg (by linarith), hu, min_eq_right (by linarith)]
  ring

/-- One step along an arc inside an open set off `y` does not decrease the angle. -/
theorem rayCircleAngle_le_of_arcStep {U : Opens rayCircleSet} (hU : rayCircleY ∉ U)
    {x z : rayCircleSet} (h : arcStep rayCircleγ U x z) : rayCircleAngle x ≤ rayCircleAngle z := by
  obtain ⟨i, s, t, hs, hst, ht, rfl, rfl, hU'⟩ := h
  cases i with
  | up =>
    rw [rayCircleAngle_up ⟨hs, hst.trans ht⟩, rayCircleAngle_up ⟨hs.trans hst, ht⟩]
    exact mul_le_mul_of_nonneg_left hst pi_pos.le
  | low =>
    have hs0 : 0 < s := by
      rcases hs.lt_or_eq with h | h
      · exact h
      · exfalso
        have hmem := hU' s ⟨le_rfl, hst⟩
        rw [← h, rayCircleγ_low_zero] at hmem
        exact hU hmem
    rw [rayCircleAngle_low ⟨hs0, hst.trans ht⟩, rayCircleAngle_low ⟨hs0.trans_le hst, ht⟩]
    nlinarith [pi_pos]
  | ray n =>
    rw [rayCircleAngle_ray n (hst.trans ht), rayCircleAngle_ray n ht]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **The angle does not decrease along `≤_U`, for `U` off `y`.** -/
theorem rayCircleAngle_le_of_le {U : Opens rayCircleSet} (hU : rayCircleY ∉ U)
    {x z : rayCircleSet} (h : rayCircle.le U x z) : rayCircleAngle x ≤ rayCircleAngle z := by
  rcases (arcCausality_le (γ := rayCircleγ)).1 h with ⟨-, rfl⟩ | hT
  · exact le_rfl
  · clear h
    induction hT with
    | single h => exact rayCircleAngle_le_of_arcStep hU h
    | tail _ h ih => exact ih.trans (rayCircleAngle_le_of_arcStep hU h)

theorem continuousOn_rayCircleAngle : ContinuousOn rayCircleAngle {rayCircleY}ᶜ := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  have hslit : rayCircleC p ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff, rayCircleC_re, rayCircleC_im]
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hp
    rcases p.2 with hcirc | ⟨hu, -⟩
    · have hcirc' : p.1.1 ^ 2 + p.1.2 ^ 2 = 1 := hcirc
      rw [h2] at hcirc'
      have hu : (p.1.1 + 1) * (p.1.1 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 hu with hu | hu
      · exact Subtype.ext (Prod.ext (show p.1.1 = -1 by linarith) h2)
      · linarith
    · linarith
  have h1 : ContinuousAt (fun p => Complex.arg (rayCircleC p)) p :=
    (Complex.continuousAt_arg hslit).comp continuous_rayCircleC.continuousAt
  have h2 : Continuous fun p : rayCircleSet => min 0 (1 - p.1.1) := by fun_prop
  exact h1.add h2.continuousAt

theorem rayCircleAngle_le_pi (p : rayCircleSet) : rayCircleAngle p ≤ π := by
  exact add_le_of_le_of_nonpos (Complex.arg_le_pi _) (min_le_left _ _)

/-! ## 5. Two standard curves: along the ray then round, and round from `y` -/

/-- Inward along the ray, then counterclockwise round the circle from `q`:
`(1 - τ, 0)` for `τ ≤ 0`, `(cos τ, sin τ)` for `τ ≥ 0`. -/
noncomputable def rayCirclePathRay (τ : ℝ) : ℝ × ℝ := (cos (max τ 0) - min τ 0, sin (max τ 0))

theorem rayCirclePathRay_mem (τ : ℝ) : rayCirclePathRay τ ∈ rayCircleSet := by
  rcases le_total τ 0 with hτ | hτ
  · refine Or.inr ⟨?_, ?_⟩
    · show 1 ≤ cos (max τ 0) - min τ 0
      rw [max_eq_right hτ, min_eq_left hτ, cos_zero]; linarith
    · show sin (max τ 0) = 0
      rw [max_eq_right hτ, sin_zero]
  · refine Or.inl ?_
    show (cos (max τ 0) - min τ 0) ^ 2 + sin (max τ 0) ^ 2 = 1
    rw [max_eq_left hτ, min_eq_right hτ, sub_zero, cos_sq_add_sin_sq]

/-- The standard curve through the ray. -/
noncomputable def rayCircleCurveRay (τ : ℝ) : rayCircleSet :=
  ⟨rayCirclePathRay τ, rayCirclePathRay_mem τ⟩

/-- The standard curve round the circle: `(cos τ, sin τ)`. -/
noncomputable def rayCircleCurveLow (τ : ℝ) : rayCircleSet :=
  ⟨(cos τ, sin τ), Or.inl (cos_sq_add_sin_sq τ)⟩

theorem rayCircleCurveRay_pi : rayCircleCurveRay π = rayCircleY := by
  apply Subtype.ext
  show rayCirclePathRay π = (-1, 0)
  simp [rayCirclePathRay, max_eq_left pi_pos.le, min_eq_right pi_pos.le]

theorem rayCircleCurveLow_pi : rayCircleCurveLow π = rayCircleY := by
  apply Subtype.ext
  show ((cos π, sin π) : ℝ × ℝ) = (-1, 0)
  simp

theorem continuous_rayCircleCurveRay : Continuous rayCircleCurveRay :=
  Continuous.subtype_mk (by unfold rayCirclePathRay; fun_prop) _

theorem continuous_rayCircleCurveLow : Continuous rayCircleCurveLow :=
  Continuous.subtype_mk (by fun_prop) _

/-- A ray piece is the curve through the ray, reparametrised. -/
theorem rayCircleγ_ray_eq (n : ℕ) {r : ℝ} (hr : r ≤ 1) :
    rayCircleγ (.ray n) r = rayCircleCurveRay (n * (r - 1)) := by
  have h1 : (n : ℝ) * (r - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)
  apply Subtype.ext
  show ((1 + n * max (1 - r) 0, 0) : ℝ × ℝ) = rayCirclePathRay (n * (r - 1))
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - r)]
  simp only [rayCirclePathRay, max_eq_right h1, min_eq_left h1, cos_zero, sin_zero]
  exact Prod.ext (by ring) rfl

/-- The upper half-circle is the curve through the ray, past `q`, reparametrised. -/
theorem rayCircleγ_up_eq_ray {r : ℝ} (hr : 0 ≤ r) :
    rayCircleγ .up r = rayCircleCurveRay (π * r) := by
  have h1 : 0 ≤ π * r := mul_nonneg pi_pos.le hr
  apply Subtype.ext
  show ((cos (π * r), sin (π * r)) : ℝ × ℝ) = rayCirclePathRay (π * r)
  simp only [rayCirclePathRay, max_eq_left h1, min_eq_right h1, sub_zero]

/-- The upper half-circle is the curve round the circle, reparametrised. -/
theorem rayCircleγ_up_eq_low (r : ℝ) : rayCircleγ .up r = rayCircleCurveLow (π * r) := rfl

/-- The lower half-circle is the curve round the circle, reparametrised. -/
theorem rayCircleγ_low_eq_low (r : ℝ) : rayCircleγ .low r = rayCircleCurveLow (π * r - π) := by
  apply Subtype.ext
  show ((-cos (π * r), -sin (π * r)) : ℝ × ℝ) = (cos (π * r - π), sin (π * r - π))
  rw [cos_sub_pi, sin_sub_pi]

/-- Along the ray, `s ≤ s' ≤ 0`: one step along a ray piece. -/
theorem rayCircle_le_curveRay_of_nonpos {N : Opens rayCircleSet} {s s' : ℝ} (hss' : s ≤ s')
    (hs' : s' ≤ 0) (hN : rayCircleCurveRay '' Icc s s' ⊆ N) :
    rayCircle.le N (rayCircleCurveRay s) (rayCircleCurveRay s') := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-s)
  have hnpos : (0 : ℝ) < n := by linarith
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hσ₁ : 0 ≤ 1 + s / n := by
    have : -1 < s / n := by rw [lt_div_iff₀ hnpos]; linarith
    linarith
  have hσ₂ : 1 + s' / n ≤ 1 := by
    have : s' / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs' hnpos.le
    linarith
  have h12 : 1 + s / n ≤ 1 + s' / n := by
    have := div_le_div_of_nonneg_right hss' hnpos.le; linarith
  refine arcStep.le ⟨.ray n, 1 + s / n, 1 + s' / n, hσ₁, h12, hσ₂, ?_, ?_, fun r hr => ?_⟩
  · rw [rayCircleγ_ray_eq n (h12.trans hσ₂), show (n : ℝ) * (1 + s / n - 1) = s by field_simp; ring]
  · rw [rayCircleγ_ray_eq n hσ₂, show (n : ℝ) * (1 + s' / n - 1) = s' by field_simp; ring]
  · rw [rayCircleγ_ray_eq n (hr.2.trans hσ₂)]
    apply hN
    refine ⟨n * (r - 1), ⟨?_, ?_⟩, rfl⟩
    · have := mul_le_mul_of_nonneg_left (show s / n ≤ r - 1 by linarith [hr.1]) hnpos.le
      rwa [mul_div_cancel₀ _ hn0] at this
    · have := mul_le_mul_of_nonneg_left (show r - 1 ≤ s' / n by linarith [hr.2]) hnpos.le
      rwa [mul_div_cancel₀ _ hn0] at this

/-- Past `q`, `0 ≤ s ≤ s' ≤ π`: one step along the upper half-circle. -/
theorem rayCircle_le_curveRay_of_nonneg {N : Opens rayCircleSet} {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') (hs' : s' ≤ π) (hN : rayCircleCurveRay '' Icc s s' ⊆ N) :
    rayCircle.le N (rayCircleCurveRay s) (rayCircleCurveRay s') := by
  have hpi := pi_pos
  refine arcStep.le ⟨.up, s / π, s' / π, div_nonneg hs hpi.le,
    div_le_div_of_nonneg_right hss' hpi.le, (div_le_one hpi).2 hs', ?_, ?_, fun r hr => ?_⟩
  · rw [rayCircleγ_up_eq_ray (div_nonneg hs hpi.le), mul_div_cancel₀ _ hpi.ne']
  · rw [rayCircleγ_up_eq_ray (div_nonneg (hs.trans hss') hpi.le), mul_div_cancel₀ _ hpi.ne']
  · have hr0 : 0 ≤ r := (div_nonneg hs hpi.le).trans hr.1
    rw [rayCircleγ_up_eq_ray hr0]
    apply hN
    refine ⟨π * r, ⟨?_, ?_⟩, rfl⟩
    · have := mul_le_mul_of_nonneg_left hr.1 hpi.le
      rwa [mul_div_cancel₀ _ hpi.ne'] at this
    · have := mul_le_mul_of_nonneg_left hr.2 hpi.le
      rwa [mul_div_cancel₀ _ hpi.ne'] at this

/-- From `y` to `q`, `-π ≤ s ≤ s' ≤ 0`: one step along the lower half-circle. -/
theorem rayCircle_le_curveLow_of_nonpos {N : Opens rayCircleSet} {s s' : ℝ} (hs : -π ≤ s)
    (hss' : s ≤ s') (hs' : s' ≤ 0) (hN : rayCircleCurveLow '' Icc s s' ⊆ N) :
    rayCircle.le N (rayCircleCurveLow s) (rayCircleCurveLow s') := by
  have hpi := pi_pos
  refine arcStep.le ⟨.low, (s + π) / π, (s' + π) / π, div_nonneg (by linarith) hpi.le,
    div_le_div_of_nonneg_right (by linarith) hpi.le, (div_le_one hpi).2 (by linarith), ?_, ?_,
    fun r hr => ?_⟩
  · rw [rayCircleγ_low_eq_low, show π * ((s + π) / π) - π = s by field_simp; ring]
  · rw [rayCircleγ_low_eq_low, show π * ((s' + π) / π) - π = s' by field_simp; ring]
  · rw [rayCircleγ_low_eq_low]
    apply hN
    refine ⟨π * r - π, ⟨?_, ?_⟩, rfl⟩
    · have := mul_le_mul_of_nonneg_left hr.1 hpi.le
      rw [mul_div_cancel₀ _ hpi.ne'] at this
      linarith
    · have := mul_le_mul_of_nonneg_left hr.2 hpi.le
      rw [mul_div_cancel₀ _ hpi.ne'] at this
      linarith

/-- From `q` to `y`, `0 ≤ s ≤ s' ≤ π`: one step along the upper half-circle. -/
theorem rayCircle_le_curveLow_of_nonneg {N : Opens rayCircleSet} {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') (hs' : s' ≤ π) (hN : rayCircleCurveLow '' Icc s s' ⊆ N) :
    rayCircle.le N (rayCircleCurveLow s) (rayCircleCurveLow s') := by
  have hpi := pi_pos
  refine arcStep.le ⟨.up, s / π, s' / π, div_nonneg hs hpi.le,
    div_le_div_of_nonneg_right hss' hpi.le, (div_le_one hpi).2 hs', ?_, ?_, fun r hr => ?_⟩
  · rw [rayCircleγ_up_eq_low, mul_div_cancel₀ _ hpi.ne']
  · rw [rayCircleγ_up_eq_low, mul_div_cancel₀ _ hpi.ne']
  · rw [rayCircleγ_up_eq_low]
    apply hN
    refine ⟨π * r, ⟨?_, ?_⟩, rfl⟩
    · have := mul_le_mul_of_nonneg_left hr.1 hpi.le
      rwa [mul_div_cancel₀ _ hpi.ne'] at this
    · have := mul_le_mul_of_nonneg_left hr.2 hpi.le
      rwa [mul_div_cancel₀ _ hpi.ne'] at this

/-- **The curve through the ray is a causal curve over `]-∞, π]`.** -/
theorem rayCircleCurveRay_causalCurveIn : rayCircle.CausalCurveIn ⊤ (Iic π) rayCircleCurveRay := by
  refine Causality.causalCurveIn_top_of_pieces continuous_rayCircleCurveRay ⟨0, pi_pos.le⟩
    ordConnected_Iic ?_
  intro s _ s' hs' hss' N hN
  rcases le_total s' 0 with h0 | h0
  · exact rayCircle_le_curveRay_of_nonpos hss' h0 hN
  rcases le_total 0 s with h1 | h1
  · exact rayCircle_le_curveRay_of_nonneg h1 hss' hs' hN
  · exact rayCircle.le_trans
      (rayCircle_le_curveRay_of_nonpos h1 le_rfl ((image_mono (Icc_subset_Icc le_rfl h0)).trans hN))
      (rayCircle_le_curveRay_of_nonneg le_rfl h0 hs'
        ((image_mono (Icc_subset_Icc h1 le_rfl)).trans hN))

/-- **The curve round the circle is a causal curve over `[-π, π]`.** -/
theorem rayCircleCurveLow_causalCurveIn :
    rayCircle.CausalCurveIn ⊤ (Icc (-π) π) rayCircleCurveLow := by
  refine Causality.causalCurveIn_top_of_pieces continuous_rayCircleCurveLow
    ⟨0, ⟨by linarith [pi_pos], pi_pos.le⟩⟩ ordConnected_Icc ?_
  intro s hs s' hs' hss' N hN
  rcases le_total s' 0 with h0 | h0
  · exact rayCircle_le_curveLow_of_nonpos hs.1 hss' h0 hN
  rcases le_total 0 s with h1 | h1
  · exact rayCircle_le_curveLow_of_nonneg h1 hss' hs'.2 hN
  · exact rayCircle.le_trans
      (rayCircle_le_curveLow_of_nonpos hs.1 h1 le_rfl
        ((image_mono (Icc_subset_Icc le_rfl h0)).trans hN))
      (rayCircle_le_curveLow_of_nonneg le_rfl h0 hs'.2
        ((image_mono (Icc_subset_Icc h1 le_rfl)).trans hN))

theorem rayCircle_circle_of_le_one {p : rayCircleSet} (hu : p.1.1 ≤ 1) :
    p.1.1 ^ 2 + p.1.2 ^ 2 = 1 := by
  rcases p.2 with h | ⟨h1, h2⟩
  · exact h
  · rw [le_antisymm hu h1, h2]; norm_num

theorem rayCircle_le_one_of_circle {p : rayCircleSet} (h : p.1.1 ^ 2 + p.1.2 ^ 2 = 1) :
    p.1.1 ≤ 1 := by
  nlinarith [sq_nonneg p.1.2]

theorem rayCircleC_norm_of_circle {p : rayCircleSet} (h : p.1.1 ^ 2 + p.1.2 ^ 2 = 1) :
    ‖rayCircleC p‖ = 1 := by
  rw [rayCircleC, Complex.norm_add_mul_I, h, Real.sqrt_one]

/-- On the circle the angle is the argument. -/
theorem rayCircleAngle_of_circle {p : rayCircleSet} (h : p.1.1 ^ 2 + p.1.2 ^ 2 = 1) :
    rayCircleAngle p = Complex.arg (rayCircleC p) := by
  unfold rayCircleAngle
  rw [min_eq_left (by linarith [rayCircle_le_one_of_circle h]), add_zero]

theorem rayCircleCurveLow_arg {p : rayCircleSet} (h : p.1.1 ^ 2 + p.1.2 ^ 2 = 1) :
    rayCircleCurveLow (Complex.arg (rayCircleC p)) = p := by
  have hn := rayCircleC_norm_of_circle h
  have hne : rayCircleC p ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  apply Subtype.ext
  show ((cos (Complex.arg (rayCircleC p)), sin (Complex.arg (rayCircleC p))) : ℝ × ℝ) = p.1
  rw [Complex.cos_arg hne, Complex.sin_arg, hn, div_one, div_one, rayCircleC_re, rayCircleC_im]

/-- **Off the open lower half-circle, the curve through the ray at the angle of `p` is `p`.** -/
theorem rayCircleCurveRay_angle {p : rayCircleSet} (hv : 0 ≤ p.1.2) :
    rayCircleCurveRay (rayCircleAngle p) = p := by
  rcases p.2 with hcirc | ⟨hu, hv0⟩
  · have hcirc' : p.1.1 ^ 2 + p.1.2 ^ 2 = 1 := hcirc
    rw [rayCircleAngle_of_circle hcirc']
    have ha : 0 ≤ Complex.arg (rayCircleC p) :=
      Complex.arg_nonneg_iff.2 (by rw [rayCircleC_im]; exact hv)
    have hRL : rayCircleCurveRay (Complex.arg (rayCircleC p)) =
        rayCircleCurveLow (Complex.arg (rayCircleC p)) := by
      apply Subtype.ext
      show rayCirclePathRay _ = ((cos _, sin _) : ℝ × ℝ)
      simp only [rayCirclePathRay, max_eq_left ha, min_eq_right ha, sub_zero]
    rw [hRL]; exact rayCircleCurveLow_arg hcirc'
  · have hC : rayCircleC p = (p.1.1 : ℂ) := by rw [rayCircleC, hv0]; simp
    have hang : rayCircleAngle p = 1 - p.1.1 := by
      unfold rayCircleAngle
      rw [hC, Complex.arg_ofReal_of_nonneg (by linarith), min_eq_right (by linarith), zero_add]
    rw [hang]
    have h1 : 1 - p.1.1 ≤ 0 := by linarith
    apply Subtype.ext
    show rayCirclePathRay (1 - p.1.1) = p.1
    simp only [rayCirclePathRay, max_eq_right h1, min_eq_left h1, cos_zero, sin_zero]
    exact Prod.ext (by ring) hv0.symm

/-- **On the circle, the curve round the circle at the angle of `p` is `p`.** -/
theorem rayCircleCurveLow_angle {p : rayCircleSet} (hu : p.1.1 ≤ 1) :
    rayCircleCurveLow (rayCircleAngle p) = p := by
  have h := rayCircle_circle_of_le_one hu
  rw [rayCircleAngle_of_circle h]; exact rayCircleCurveLow_arg h

/-! ## 6. `{y}` is a Cauchy surface -/

/-- **A causal curve missing `y` is extensible.** Off `y` the angle does not decrease along the
curve. The curve cannot meet both the open ray and the open lower half-circle (both have negative
angle, and they are disjoint and open), so it lies on one of the two standard curves, at its
angle, and the standard curve goes on to `y` at angle `π`. -/
theorem rayCircle_extensible_of_forall_ne {I : Set ℝ} {c : ℝ → rayCircleSet}
    (hc : rayCircle.CausalCurveIn ⊤ I c) (hmiss : ∀ t ∈ I, c t ≠ rayCircleY) :
    rayCircle.Extensible ⊤ I c := by
  set N : Opens rayCircleSet := ⟨{rayCircleY}ᶜ, isOpen_compl_singleton⟩ with hN
  have hYN : rayCircleY ∉ N := fun h => h rfl
  have hcN : rayCircle.CausalCurveIn N I c :=
    ⟨hc.nonempty, hc.ordConnected, fun a ha b hb =>
      CurveOn.restrict (hc.curve a ha b hb) le_rfl le_rfl le_top
        (fun t ht => hmiss t (hc.ordConnected.out ha hb ht))⟩
  have hmono : MonotoneOn (rayCircleAngle ∘ c) I := fun x hx y hy hxy =>
    rayCircleAngle_le_of_le hYN (hcN.le_of_le hx hy hxy)
  have hcontc : ContinuousOn c I := hc.continuousOn_interval
  have hcont : ContinuousOn (rayCircleAngle ∘ c) I :=
    continuousOn_rayCircleAngle.comp hcontc (fun t ht => hmiss t ht)
  -- a negative angle: on the open lower half-circle or on the open ray
  have hneg : ∀ p : rayCircleSet, rayCircleAngle p < 0 → p.1.2 < 0 ∨ 1 < p.1.1 := by
    intro p hp
    by_contra hcon
    push Not at hcon
    obtain ⟨hv, hu⟩ := hcon
    rw [rayCircleAngle_of_circle (rayCircle_circle_of_le_one hu)] at hp
    exact absurd (Complex.arg_nonneg_iff.2 (by rw [rayCircleC_im]; exact hv)) (not_le.2 hp)
  -- the curve does not meet both the open lower half-circle and the open ray
  have hdich : (∀ t ∈ I, 0 ≤ (c t).1.2) ∨ (∀ t ∈ I, (c t).1.1 ≤ 1) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨t₁, ht₁, hv₁⟩, ⟨t₂, ht₂, hu₂⟩⟩ := hcon
    have ha₁ : rayCircleAngle (c t₁) < 0 := by
      have hcirc : (c t₁).1.1 ^ 2 + (c t₁).1.2 ^ 2 = 1 := by
        rcases (c t₁).2 with h | ⟨-, h⟩
        · exact h
        · linarith
      rw [rayCircleAngle_of_circle hcirc]
      exact Complex.arg_neg_iff.2 (by rw [rayCircleC_im]; exact hv₁)
    have ha₂ : rayCircleAngle (c t₂) < 0 := by
      rcases (c t₂).2 with h | ⟨-, h⟩
      · linarith [rayCircle_le_one_of_circle (p := c t₂) h]
      · unfold rayCircleAngle
        have hC : rayCircleC (c t₂) = ((c t₂).1.1 : ℂ) := by rw [rayCircleC, h]; simp
        rw [hC, Complex.arg_ofReal_of_nonneg (by linarith), min_eq_right (by linarith)]
        linarith
    have haI : min t₁ t₂ ∈ I := by
      rcases min_choice t₁ t₂ with h | h <;> rw [h] <;> assumption
    have hbI : max t₁ t₂ ∈ I := by
      rcases max_choice t₁ t₂ with h | h <;> rw [h] <;> assumption
    have hbneg : rayCircleAngle (c (max t₁ t₂)) < 0 := by
      rcases max_choice t₁ t₂ with h | h <;> rw [h] <;> assumption
    have hab : Icc (min t₁ t₂) (max t₁ t₂) ⊆ I := hc.ordConnected.out haI hbI
    have hall : ∀ t ∈ Icc (min t₁ t₂) (max t₁ t₂), rayCircleAngle (c t) < 0 := fun t ht =>
      (hmono (hab ht) hbI ht.2).trans_lt hbneg
    have hpre : IsPreconnected (c '' Icc (min t₁ t₂) (max t₁ t₂)) :=
      isPreconnected_Icc.image c (hcontc.mono hab)
    have hUo : IsOpen {p : rayCircleSet | p.1.2 < 0} :=
      isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const
    have hVo : IsOpen {p : rayCircleSet | 1 < p.1.1} :=
      isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val)
    obtain ⟨_, ⟨t, -, rfl⟩, hU, hV⟩ := hpre _ _ hUo hVo
      (by rintro _ ⟨t, ht, rfl⟩; exact hneg _ (hall t ht))
      ⟨c t₁, ⟨t₁, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩, hv₁⟩
      ⟨c t₂, ⟨t₂, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩, hu₂⟩
    have hU' : (c t).1.2 < 0 := hU
    have hV' : 1 < (c t).1.1 := hV
    rcases (c t).2 with h | ⟨-, h⟩
    · linarith [rayCircle_le_one_of_circle (p := c t) h]
    · linarith
  rcases hdich with hv | hu
  · exact Causality.extensible_of_graph rayCircleCurveRay_causalCurveIn hc hmono hcont
      (fun t _ => rayCircleAngle_le_pi (c t)) (fun t ht => rayCircleCurveRay_angle (hv t ht))
      (mem_Iic.2 le_rfl) (fun t _ => rayCircleAngle_le_pi (c t))
      (fun t ht => by rw [rayCircleCurveRay_pi]; exact (hmiss t ht).symm)
  · have hJ : MapsTo (rayCircleAngle ∘ c) I (Icc (-π) π) := by
      intro t ht
      refine ⟨?_, rayCircleAngle_le_pi _⟩
      show -π ≤ rayCircleAngle (c t)
      rw [rayCircleAngle_of_circle (rayCircle_circle_of_le_one (hu t ht))]
      exact (Complex.neg_pi_lt_arg _).le
    exact Causality.extensible_of_graph rayCircleCurveLow_causalCurveIn hc hmono hcont hJ
      (fun t ht => rayCircleCurveLow_angle (hu t ht)) ⟨by linarith [pi_pos], le_rfl⟩
      (fun t _ => rayCircleAngle_le_pi (c t))
      (fun t ht => by rw [rayCircleCurveLow_pi]; exact (hmiss t ht).symm)

/-- **`{y}` is a Cauchy surface** of the ray glued to the circle: every inextensible causal curve
meets `y`, and meets `{y}` in one point. -/
theorem rayCircle_isCauchySurface_Y : rayCircle.IsCauchySurface {rayCircleY} := by
  intro I c hc
  refine ⟨rayCircleY, ⟨?_, rfl⟩, fun x hx => hx.2⟩
  by_contra hno
  exact hc.2 (rayCircle_extensible_of_forall_ne hc.1 fun t ht he => hno ⟨t, ht, he⟩)

/-! ## 7. The ray: past-inextensible, through `J⁺(y)` at `q`, missing `y` -/

/-- **The ray**, run inward and then resting at `q`: `(1 - t, 0)` for `t ≤ 0`, `q` for `t ≥ 0`. -/
noncomputable def rayCircleRay (t : ℝ) : rayCircleSet := rayCircleCurveRay (min t 0)

theorem rayCircleRay_fst (t : ℝ) : (rayCircleRay t).1.1 = 1 - min t 0 := by
  have h : min t 0 ≤ 0 := min_le_right t 0
  show cos (max (min t 0) 0) - min (min t 0) 0 = 1 - min t 0
  rw [max_eq_right h, min_eq_left h, cos_zero]

theorem rayCircleRay_causalCurveIn : rayCircle.CausalCurveIn ⊤ univ rayCircleRay := by
  have h := rayCircleCurveRay_causalCurveIn.comp_monotoneOn (h := fun t => min t 0)
    (I' := univ) univ_nonempty ordConnected_univ (fun _ _ _ _ h => min_le_min_right 0 h)
    (continuous_id.min continuous_const).continuousOn
    (fun t _ => (min_le_right t 0).trans pi_pos.le)
  exact h

/-- **The ray is past-inextensible**: it has no limit at `-∞`. -/
theorem rayCircleRay_pastInextensible : rayCircle.PastInextensible ⊤ univ rayCircleRay := by
  refine LineDevelopment.pastInextensible_of_not_tendsto_atBot rayCircleRay_causalCurveIn
    fun x _ hx => ?_
  have h1 : Tendsto (fun t => (rayCircleRay t).1.1) atBot (𝓝 x.1.1) :=
    ((continuous_fst.comp continuous_subtype_val).tendsto x).comp hx
  have h2 : Tendsto (fun t => (rayCircleRay t).1.1) atBot atTop := by
    refine tendsto_atTop_mono (fun t => ?_) tendsto_neg_atBot_atTop
    show -t ≤ (rayCircleRay t).1.1
    rw [rayCircleRay_fst]; linarith [min_le_left t 0]
  exact not_tendsto_nhds_of_tendsto_atTop h2 _ h1

theorem rayCircleRay_zero : rayCircleRay 0 = rayCircleQ := by
  apply Subtype.ext
  show rayCirclePathRay (min 0 0) = (1, 0)
  simp [rayCirclePathRay]

/-- `q ∈ J⁺({y})`, along the lower half-circle. -/
theorem rayCircleRay_zero_mem_Jplus : rayCircleRay 0 ∈ rayCircle.Jplus ⊤ {rayCircleY} := by
  exact ⟨rayCircleY, rfl, by rw [rayCircleRay_zero]; exact rayCircle_le_Y_Q⟩

/-- The ray misses `y`. -/
theorem rayCircleRay_ne_Y (t : ℝ) : rayCircleRay t ≠ rayCircleY := by
  intro h
  have h1 := congrArg (fun p : rayCircleSet => p.1.1) h
  have h2 : (rayCircleY).1.1 = -1 := rfl
  rw [rayCircleRay_fst, h2] at h1
  linarith [min_le_right t 0]

/-! ## 8. The witness -/

/-- **Sbierski's (2.4) needs `≤` antisymmetric** (the target's conjoined witness). The ray glued
to the circle is Hausdorff and second countable; its causality has `≪` empty, is causally
arc-connected and absolutely minimal (and on every open set, for every cover); `≤` is not
antisymmetric, since `q ≤ y ≤ q` with `q ≠ y`; `{y}` is a Cauchy surface; and the ray is a
past-inextensible causal curve whose point at `0` is `q ∈ J⁺({y})`, and which misses `{y}`. So every
hypothesis of `Causality.PastInextensible.exists_mem_of_mem_Jplus_of_isCausal` but `is_causal`
holds (T2 for T1), and its conclusion fails. -/
theorem rayCircle_separates_pastInextensible_meets :
    T2Space rayCircleSet ∧ SecondCountableTopology rayCircleSet ∧
      (∀ U x y, ¬ rayCircle.lt U x y) ∧
      rayCircle.CausallyArcConnected ∧ rayCircle.AbsolutelyMinimal ∧
      (∀ W : Opens rayCircleSet, rayCircle.AbsolutelyMinimalOn W) ∧
      ¬ rayCircle.IsCausal ∧
      (rayCircle.le ⊤ rayCircleQ rayCircleY ∧ rayCircle.le ⊤ rayCircleY rayCircleQ ∧
        rayCircleQ ≠ rayCircleY) ∧
      rayCircle.IsCauchySurface {rayCircleY} ∧
      rayCircle.PastInextensible ⊤ univ rayCircleRay ∧ rayCircleRay 0 = rayCircleQ ∧
      (∃ t ∈ (univ : Set ℝ), rayCircleRay t ∈ rayCircle.Jplus ⊤ {rayCircleY}) ∧
      ¬ ∃ t ∈ (univ : Set ℝ), rayCircleRay t ∈ ({rayCircleY} : Set rayCircleSet) := by
  exact ⟨inferInstance, inferInstance, fun _ _ _ => arcCausality_not_lt,
    rayCircle_causallyArcConnected, rayCircle_absolutelyMinimal, rayCircle_absolutelyMinimalOn,
    rayCircle_not_isCausal, ⟨rayCircle_le_Q_Y, rayCircle_le_Y_Q, rayCircleQ_ne_Y⟩,
    rayCircle_isCauchySurface_Y, rayCircleRay_pastInextensible, rayCircleRay_zero,
    ⟨0, trivial, rayCircleRay_zero_mem_Jplus⟩, fun ⟨t, _, ht⟩ => rayCircleRay_ne_Y t ht⟩

/-- **(2.4) without antisymmetry is false**: on a Hausdorff, second countable space, with `S` a
Cauchy surface of `M` and the causality causally arc-connected, a past-inextensible causal curve
with a point in `J⁺(S)` need not meet `S` (the ray glued to the circle). -/
theorem not_pastInextensible_exists_mem_of_mem_Jplus_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M) (S : Set M) (I : Set ℝ) (σ : ℝ → M), C.IsCauchySurface S →
        C.CausallyArcConnected → C.PastInextensible ⊤ I σ → (∃ t ∈ I, σ t ∈ C.Jplus ⊤ S) →
          ∃ t ∈ I, σ t ∈ S := fun h => by
  obtain ⟨-, -, -, hC, -, -, -, -, hS, hσ, -, hJ, hno⟩ :=
    rayCircle_separates_pastInextensible_meets
  exact hno (h rayCircleSet rayCircle {rayCircleY} univ rayCircleRay hS hC hσ hJ)

end Causal
