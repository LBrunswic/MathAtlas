import Causal.CExtConnexeCauchy.SubArc

/-!
# Extending a causal curve along a causal curve it lies on

Programme target `T-abs-extensible-comp-hoist` (`programme/roadmap.toml`; layer 1: it imports
`Causal.CExtConnexeCauchy.SubArc` only, ETT-layer; no model; no metric notion in a statement; no
hypothesis on the causality). There is no statement of `ETT.tex` behind it, so **no label is
marked**. The module holds the model-free curve lemmas that `T-abs-meets-cauchy-antisymmetry-sharp`
proved for its ray glued to a circle, hoisted by `T-abs-extensible-comp-hoist` out of
`Causal.MeetsCauchyAntisymmetrySharp` (its § 1, "Three model-free lemmas on curves"), so that they
can be used without importing that witness.

> Causal.Causality.extensible_of_eq_comp_monotoneOn: if c = γ ∘ h on I, with h continuous and
> non-decreasing into J and γ a causal curve over J that goes on to a value c does not take, then
> c is extensible, with no hypothesis on the causality. Its bounded case becomes
> extensible_of_eq_comp_monotoneOn_of_bddAbove. CausalCurveIn.continuousOn_interval and
> causalCurveIn_top_of_pieces move under their names (the target's title,
> `programme/roadmap.toml`)

## What moved, and the two renames

Four theorems, from `Causal.MeetsCauchyAntisymmetrySharp` to here, in the same scope (namespace
`Causal.Causality`, `variable {M : Type*} [TopologicalSpace M] {C : Causality M}`, the same `open`
line), each statement unchanged but for the renamed names:

* `Causality.extensible_of_graph` is now `Causality.extensible_of_eq_comp_monotoneOn`;
* `Causality.extensible_of_graph_of_bddAbove` is now
  `Causality.extensible_of_eq_comp_monotoneOn_of_bddAbove`;
* `Causality.causalCurveIn_top_of_pieces` and `Causality.CausalCurveIn.continuousOn_interval`
  keep their names.

The old names named a graph the statement does not have; what it has is `c = γ ∘ h` with `h`
monotone (the audit of `T-abs-meets-cauchy-antisymmetry-sharp`). No alias of the old names is left.

## What is proved (no `sorry`)

With no hypothesis on the causality `C` and none on the space `M` beyond its topology:

1. **Extension along a causal curve** (`extensible_of_eq_comp_monotoneOn`): if `c` is a causal
   curve of `W` over `I` with `c = γ ∘ h` on `I`, `h` continuous and non-decreasing on `I` and
   mapping `I` into `J`, `γ` a causal curve of `W` over `J`, and `t' ∈ J` above `h '' I` with
   `γ t'` a value `c` does not take, then `c` is extensible in `W`. The parameter is first compressed by `Real.arctan`, then the bounded case
   applies, and `Extensible.of_comp` (`Causal.Inextensible`) brings the extension back.
2. **Its bounded case** (`extensible_of_eq_comp_monotoneOn_of_bddAbove`), `I` bounded above: the
   new curve is `γ ∘ g` over `I ∪ [b, b + (t' - k)]`, `b = sup I`, `k = sup h(I)`, with `g = h`
   below `b` and affine from `b` on, a causal curve by `CausalCurveIn.comp_monotoneOn`
   (`Causal.CExtConnexeCauchy.SubArc`); its value at `b + (t' - k)` is `γ t'`.
3. **A continuous map whose pieces are related** (`causalCurveIn_top_of_pieces`): if `J` is a
   nonempty order-connected set, `γ : ℝ → M` is continuous and `γ s ≤_N γ s'` whenever `s ≤ s'` in
   `J` and `γ '' [s, s'] ⊆ N`, `N` open, then `γ` is a causal curve of `M` (of `⊤`) over `J`.
4. **Continuity** (`CausalCurveIn.continuousOn_interval`): a causal curve over an interval is
   continuous on it, from its continuity on each closed sub-interval
   (`CausalCurveIn.continuousOn_Icc`, `Causal.CauchyExtension`).

## Hypothesis checklist

There is no paper statement; what the lemmas ask:

| hypothesis | here |
|---|---|
| a causality condition on `C` (`IsCausal`, `StronglyCausal`, …) | none |
| separation or countability of `M` | none |
| the curves (1, 2) | `γ` a causal curve of `W` over `J`, `c` one over `I`, `γ (h t) = c t` for `t ∈ I` |
| the reparametrisation `h` (1, 2) | `MonotoneOn h I`, `ContinuousOn h I`, `MapsTo h I J` |
| the new value (1, 2) | `t' ∈ J`, `h t ≤ t'` and `γ t' ≠ c t` for `t ∈ I` |
| `I` (2 only) | bounded above |
| the pieces (3) | `γ` continuous, `J` nonempty and order-connected, `γ s ≤_N γ s'` on each piece in an open `N` |
| continuity (4) | `c` a causal curve of `W` over `I` |

## SCOPE (disclosed)

* **Nothing marked**: no label of `ETT.tex`.
* **Metric and trigonometry in proofs only**: `Metric.isOpen_iff`, `Metric.tendsto_nhdsWithin_nhds`
  and `Real.dist_eq`, on `ℝ`, and `Real.arctan`, `Real.tan`, appear in the proofs; no statement
  mentions a metric.
* **Model-layer twins, not merged here.** `Causality.extensible_of_timeGraph_openEnd`
  (`Causal.Remarks.SingularRowsCauchyExt`, model layer, so not importable here) is the case
  `h = T ∘ c` of `extensible_of_eq_comp_monotoneOn`, which needs neither its `hbdd` nor its
  `hnomax`; the same module's `continuousOn_of_causalCurveIn` is the twin of
  `CausalCurveIn.continuousOn_interval`, under another name. That module is /atlas-team's, so
  making them corollaries is that loop's call and is not done here.
* The extension step of `Causal.MeetsCauchyAntisymmetrySharp`'s `{y}`-is-Cauchy argument
  (`rayCircle_extensible_of_forall_ne`) is the first use of `extensible_of_eq_comp_monotoneOn`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Function TopologicalSpace Topology Filter Real

/-! ## Three model-free lemmas on curves -/

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

/-- **Extension along a causal curve, bounded case**: `extensible_of_eq_comp_monotoneOn` for `I`
bounded above. The new curve is `γ ∘ g` over `I ∪ [b, b + (t' - k)]`, `b = sup I`, `k = sup h(I)`,
with `g = h` below `b` and `g = k + (· - b)` from `b` on; its value at `b + (t' - k)` is `γ t'`. -/
theorem extensible_of_eq_comp_monotoneOn_of_bddAbove {W : Opens M} {I J : Set ℝ} {c γ : ℝ → M}
    {h : ℝ → ℝ} {t' : ℝ} (hγ : C.CausalCurveIn W J γ) (hc : C.CausalCurveIn W I c)
    (hbdd : BddAbove I) (hmono : MonotoneOn h I) (hcont : ContinuousOn h I) (hJ : MapsTo h I J)
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
theorem extensible_of_eq_comp_monotoneOn {W : Opens M} {I J : Set ℝ} {c γ : ℝ → M} {h : ℝ → ℝ}
    {t' : ℝ} (hγ : C.CausalCurveIn W J γ) (hc : C.CausalCurveIn W I c)
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
    refine extensible_of_eq_comp_monotoneOn_of_bddAbove (h := h ∘ Real.tan) hγ hdc
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

end Causal
