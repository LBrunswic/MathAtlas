import Causal.FlrwType

/-!
# In a closed, antisymmetric ambient, (A) alone excludes a past boundary chart, and so does (B)

Programme target `T-abs-flrw-type-closed-ambient` (`programme/roadmap.toml`; layer 1, stream
abstract). The module imports `Causal.FlrwType` only. That module is ETT-layer, and its import
closure holds `Causal.GlobalHyperbolicity`. No model is imported, and no statement mentions a
metric. Sbierski 2312.07443 is not ledgered and has no binder, so **no label is marked**. Source:
J. Sbierski, *The C⁰-inextendibility of a class of FLRW spacetimes*,
`references/sbierski/text/sbierski2023c.txt`: Thm 1.5 (§4.1, `:1057–1144`), Prop 3.6 (`:704–739`).

> For any s0 ∈ (0, 1) we then have [ I + γ(s), M ∩ I − γ(s0 ), M = I − γ(s0 ), M . 0<s<s0
> Furthermore for each such s0 ∈ (0, 1) there exists a t0 > 0 such that {t0 } × Sd ⊆ I − γ(s0 ), M .
> (`:706–715`, Prop 3.6, as extracted; (A) and (B) of `not_pastBoundaryChart_of_flrwType` read its
> two claims)

## What is proved (no `sorry`)

1. **The theorem** `Causality.not_pastBoundaryChart_of_flrwTypeA_of_isClosed_le`. Let `M` be T2,
   with `{z | z.1 ≤_M z.2}` closed and `≤_M` antisymmetric (`C.IsCausal`), and let `W` be an open
   set with (A) of `not_pastBoundaryChart_of_flrwType`. Then `W` has a past boundary chart at no
   point. It needs no (B), no future one-connectedness, no causal arc-connectedness and no second
   countability. Its local form `not_pastBoundaryChart_of_flrwTypeA_of_closedIn` states the two
   ambient hypotheses at one open `U ≥ W ⊔ Ũ` instead of `M`: `≤_U` closed in `U × U` and
   antisymmetric (`U = ⊤` is the theorem).
2. **The corollary** `Causality.GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeA`, on every
   globally hyperbolic, tarentin T2 spacetime, by `GloballyHyperbolic.isClosed_le`.
3. **The instance check** `GloballyHyperbolic.not_flrwTypeA_of_pastBoundaryChart`: on such a
   spacetime an open set with a past boundary chart fails (A). On `𝐌^{1+n}`, `n ≥ 1`, the
   ingredients are `minkowski_isCausal`, `minkowski_tarentin`, `minkowski_globallyHyperbolic`
   (`Causal/Minkowski.lean:110, :121, :132`) and `minkowski_pastBoundaryChart`
   (`Causal.Model.MinkowskiPastBoundaryChart`). This re-derives
   `minkowski_posHalfSpace_not_flrwTypeA` by another route. That module is layer 3, so it is cited
   here and not imported.
4. **The time reversal** `not_futureBoundaryChart_of_flrwTypeA_of_isClosed_le`, its local form
   and its globally hyperbolic form, all through `C.dual`.
5. **(B) alone** `not_pastBoundaryChart_of_flrwTypeB_of_isClosed_le`, the optional report,
   proved. Take `M` T2, second countable, with `≤_M` closed and antisymmetric, and `W` causally
   arc-connected with (B). Then `W` has a past boundary chart at no point. It needs no (A) and no
   future one-connectedness. Its local, globally hyperbolic and time-reversed forms
   (`not_futureBoundaryChart_of_flrwTypeB_of_isClosed_le`) come with it, and so does
   `GloballyHyperbolic.not_flrwTypeB_of_pastBoundaryChart`, which re-derives
   `minkowski_posHalfSpace_not_flrwTypeB` on the half-space.
6. **The closing step** `PastBoundaryChartData.false_of_squeeze`. A chronal curve `σ` of `Ũ` over
   `[0, 1]`, lying in `W` on `(0, 1]` and off the chart diamond, gives a contradiction once
   `p ≤_U σ t` for every `t ∈ (0, 1]` and every `γ̃ s` lies above some `σ t`. Both theorems feed it:
   (A) through chronal futures, (B) through `(2.4)` and a split by a Cauchy surface
   (`IsCauchySurfaceOn.mem_Jplus_union_Jminus`, first proved here; moved by T-abs-sc-open-hoist,
   byte for byte under the same full name, to `Causal.CurvesExtendSecondCountable`, which this
   module reaches through `Causal.FlrwType`).
7. **Witnesses** (kb/0011). On `W = (0, ∞)` of the timelike line, both theorems apply
   (`timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeA`, `…_of_flrwTypeB`). They agree
   with `timelikeLine_not_pastBoundaryChart`.

## The fields of the chart that are used

For (A) and for (B): (i) `p ∈ Ũ`, `p ∉ W`; (ii) `V ≤ W ⊓ Ũ`; (iv) the chronal curve `γ̃` of `Ũ`
from `p` into `V`; (v) `s₀ ∈ (0, 1)`, and the closure of the diamond, compact and inside `Ũ`, to
feed (vi); (vi) at the single compact set `K` = that closure, and only its first three conjuncts.
**Neither field (iii) nor the last conjunct of (vi)** (`γ̃ 1 ≪_Ũ σ 1`) is used. Field (v) enters
once more: `I⁻(γ̃ s₀, Ũ)` is an open neighbourhood of `p` (`Causality.isOpen_Iminus`) whose
`I⁺(p, Ũ)`-part lies in `K`.

## Hypothesis checklist

| `not_pastBoundaryChart_of_flrwType` / the target | here |
|---|---|
| `M` T2 | ✓ `[T2Space M]`: for (A) only through step (a), `pastInextensible_Ioc_of_start_notMem`; for (B) also the T1 instance that `(2.4)` and the split need |
| `M` second countable | ⚠ weakened for (A): not used. ✓ carried for (B): `(2.4)` and the split |
| `W` causally arc-connected | ⚠ weakened for (A): not used. ✓ carried for (B): `(2.4)` |
| `W` future one-connected | ⚠ weakened: not used, by either theorem |
| `≤_W` antisymmetric | ⚠ strengthened (the target's hypothesis): `≤_M` antisymmetric (`C.IsCausal`), or `≤_U` for an open `U ≥ W ⊔ Ũ`; `≤_W` follows |
| — (none) | ⚠ strengthened (the target's hypothesis): `{z ∣ z.1 ≤_M z.2}` closed, or `≤_U` closed in `U × U` |
| (A) | ✓ carried, in the shape of `FlrwType.lean:318–319` (the (A)-theorem) |
| (B) | ✓ carried, in the shape of `FlrwType.lean:320` (the (B)-theorem) |
| (A) **and** (B) | ⚠ weakened: either one alone |

## SCOPE (disclosed)

* The closedness of `≤` is a hypothesis of the theorem, not a ladder node (the target's
  evidence). Antisymmetry is the node `is_causal` (`C.IsCausal`); the corollary's nodes are
  `globally_hyperbolic` and `tarentin`. The local forms state both in `U`. Their closedness is the
  shape of the scaffold's `IsCausallyClosedOn U` (`CausalScaffold.GerochEquiv`, written out here
  because a strict module cannot import the scaffold).
* **The Minkowski instance is not stated here**: `Causal.Model.MinkowskiPastBoundaryChart` is
  layer 3. `campaign/T-abs-flrw-type-closed-ambient/Probe.lean` imports it beside this module and
  checks both re-derivations.
* **What this says about separating (A) from (B).** A witness that (B) is needed must have (A), a
  chart, and an ambient whose `≤` is not closed or not antisymmetric, even on `W ⊔ Ũ`, by the
  local form. A witness that (A) is needed must have (B) and a chart; any witness for
  `not_pastBoundaryChart_of_flrwType` is second countable with `W` causally arc-connected, so it
  too must have such an ambient, by the (B)-theorem's local form.
* Sbierski's ambient `M̃` is a `C⁰` extension, and its causal relation need not be closed. His
  proof uses (A) and (B) together, with future one-connectedness and (2.4) reversed (field (iii)),
  to confine the contradiction to the chart diamond. Whether any of these is needed once the
  ambient is not closed is open: no concrete model is known. This is layer 4 (classification),
  noted and not stated.
* `causal_ladder` is not used: no statement concludes a ladder property.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Function TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W Ũ : Opens M} {p : M}

/-! ### A general lemma -/

/-- **A relatively closed causal relation pulls back to a closed set.** If `≤_U` is closed in
`U × U`, then for `F` continuous on a closed `B` with values in `U × U`, the set of `x ∈ B` with
`(F x).1 ≤_U (F x).2` is closed. -/
theorem isClosed_inter_preimage_setOf_le {X : Type*} [TopologicalSpace X] {U : Opens M}
    (hcl : closure {z : M × M | C.le U z.1 z.2} ∩ ((U : Set M) ×ˢ (U : Set M)) ⊆
      {z : M × M | C.le U z.1 z.2})
    {B : Set X} (hB : IsClosed B) {F : X → M × M} (hF : ContinuousOn F B)
    (hFU : MapsTo F B ((U : Set M) ×ˢ (U : Set M))) :
    IsClosed (B ∩ F ⁻¹' {z : M × M | C.le U z.1 z.2}) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxB : x ∈ B := hB.closure_subset (closure_mono inter_subset_left hx)
  refine ⟨hxB, hcl ⟨?_, hFU hxB⟩⟩
  have h1 : F x ∈ closure (F '' (B ∩ F ⁻¹' {z : M × M | C.le U z.1 z.2})) :=
    ((hF x hxB).mono inter_subset_left).mem_closure_image hx
  exact closure_mono ((image_mono inter_subset_right).trans (image_preimage_subset F _)) h1

/-! ### The closing step -/

namespace PastBoundaryChartData

/-- **The closing step: a chart curve squeezed onto `p`.** Let `d` be a past boundary chart of
`W` at `p`, and `U ≥ Ũ` an open set with `≤_U` closed in `U × U` and antisymmetric. Let `σ` be a
chronal curve of `Ũ` over `[0, 1]`, in `W` on `(0, 1]` and off the chart diamond
`I⁺(p, Ũ) ∩ I⁻(γ̃ s₀, Ũ)` there. Suppose that

* (3) `p ≤_U σ t` for every `t ∈ (0, 1]`;
* (4) every `γ̃ s`, `s ∈ (0, 1]`, lies above some `σ t`, `t ∈ (0, 1]`, in `≤_U`.

That is a contradiction. (2) `σ 0 ≠ p`: otherwise `σ t` enters the open `I⁻(γ̃ s₀, Ũ) ∋ p` for small
`t > 0` (continuity), while `p ≪_Ũ σ t`, so `σ t` lies in the diamond. (3) extends to `t = 0` by
closedness. In (4), a compactness limit along `s → 0` (the projection to `s` of a compact subset of
`[0, 1]²`) gives `t̄ ∈ [0, 1]` with `σ t̄ ≤_U p`. Antisymmetry then gives `σ t̄ = p`, which is
against (2) if `t̄ = 0` and against `p ∉ W` if `t̄ > 0`. Of the chart only (i), (iv) and the vertex
`s₀` of (v) are used. -/
theorem false_of_squeeze (d : C.PastBoundaryChartData W Ũ p) {U : Opens M} (hŨU : Ũ ≤ U)
    (hcl : closure {z : M × M | C.le U z.1 z.2} ∩ ((U : Set M) ×ˢ (U : Set M)) ⊆
      {z : M × M | C.le U z.1 z.2})
    (hcaus : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y)
    {σ : ℝ → M} (hσ : C.ChronalCurveOn Ũ σ 0 1) (hσW : ∀ t ∈ Ioc (0 : ℝ) 1, σ t ∈ W)
    (hσK : ∀ t ∈ Ioc (0 : ℝ) 1, σ t ∉ C.Iplus Ũ {p} ∩ C.Iminus Ũ {d.curve d.s₀})
    (h3 : ∀ t ∈ Ioc (0 : ℝ) 1, C.le U p (σ t))
    (h4 : ∀ s ∈ Ioc (0 : ℝ) 1, ∃ t ∈ Ioc (0 : ℝ) 1, C.le U (σ t) (d.curve s)) : False := by
  have hσc : ContinuousOn σ (Icc 0 1) := CurveOn.continuousOn C.isRelFamily_lt hσ
  have hγc : ContinuousOn d.curve (Icc 0 1) :=
    CurveOn.continuousOn C.isRelFamily_lt d.chronalCurveOn
  have hpU : p ∈ U := hŨU d.mem
  have h0 : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩
  -- (2) `σ 0 ≠ p`: otherwise `σ t` enters the chart diamond for small `t > 0`
  have h2 : σ 0 ≠ p := by
    intro hσ0
    have hps₀ : C.lt Ũ p (d.curve d.s₀) := by
      have := d.chronalCurveOn.lt_of_lt le_rfl d.s₀_mem.1 d.s₀_mem.2.le
      rwa [d.curve_zero] at this
    have hO : C.Iminus Ũ {d.curve d.s₀} ∈ 𝓝 (σ 0) := by
      rw [hσ0]
      exact C.isOpen_Iminus.mem_nhds (Precausality.mem_Iminus_singleton.2 hps₀)
    have hcont : ContinuousWithinAt σ (Ioc 0 1) 0 :=
      (hσc 0 ⟨le_rfl, zero_le_one⟩).mono Ioc_subset_Icc_self
    haveI : (𝓝[Ioc (0 : ℝ) 1] 0).NeBot := mem_closure_iff_nhdsWithin_neBot.1 h0
    obtain ⟨t, hσt, ht⟩ := ((hcont.eventually_mem hO).and self_mem_nhdsWithin).exists
    have hpt : C.lt Ũ p (σ t) := by
      have := hσ.lt_of_lt le_rfl ht.1 ht.2
      rwa [hσ0] at this
    exact hσK t ht ⟨Precausality.mem_Iplus_singleton.2 hpt, hσt⟩
  -- (3) at `t = 0`, by closedness: `p ≤_U σ t` on all of `[0, 1]`
  have h3' : ∀ t ∈ Icc (0 : ℝ) 1, C.le U p (σ t) := by
    have hF : ContinuousOn (fun t => (p, σ t)) (Icc (0 : ℝ) 1) := continuousOn_const.prodMk hσc
    have hcl3 := isClosed_inter_preimage_setOf_le hcl isClosed_Icc hF
      (fun t ht => ⟨hpU, hŨU (hσ.mem t ht)⟩)
    have hsub : Ioc (0 : ℝ) 1 ⊆
        Icc (0 : ℝ) 1 ∩ (fun t => (p, σ t)) ⁻¹' {z : M × M | C.le U z.1 z.2} :=
      fun t ht => ⟨Ioc_subset_Icc_self ht, h3 t ht⟩
    intro t ht
    have : t ∈ closure (Ioc (0 : ℝ) 1) := by rw [closure_Ioc zero_ne_one]; exact ht
    exact (hcl3.closure_subset (closure_mono hsub this)).2
  -- (4) a compactness limit along `s → 0`: some `σ t̄ ≤_U p`
  obtain ⟨tb, htb, htbp⟩ : ∃ t ∈ Icc (0 : ℝ) 1, C.le U (σ t) p := by
    let F : ℝ × ℝ → M × M := fun z => (σ z.1, d.curve z.2)
    have hF : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
      (hσc.comp continuousOn_fst fun z hz => hz.1).prodMk
        (hγc.comp continuousOn_snd fun z hz => hz.2)
    have hS := isClosed_inter_preimage_setOf_le hcl (isClosed_Icc.prod isClosed_Icc) hF
      (fun z hz => ⟨hŨU (hσ.mem _ hz.1), hŨU (d.chronalCurveOn.mem _ hz.2)⟩)
    have hSk := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hS inter_subset_left
    have hP := (hSk.image continuous_snd).isClosed
    have hsub : Ioc (0 : ℝ) 1 ⊆ Prod.snd '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∩
        F ⁻¹' {z : M × M | C.le U z.1 z.2}) := fun s hs => by
      obtain ⟨t, ht, hts⟩ := h4 s hs
      exact ⟨(t, s), ⟨⟨Ioc_subset_Icc_self ht, Ioc_subset_Icc_self hs⟩, hts⟩, rfl⟩
    obtain ⟨⟨t, s⟩, ⟨⟨ht, -⟩, hts⟩, hs⟩ := hP.closure_subset (closure_mono hsub h0)
    simp only at hs
    subst hs
    refine ⟨t, ht, ?_⟩
    have : C.le U (σ t) (d.curve 0) := hts
    rwa [d.curve_zero] at this
  -- antisymmetry: `σ t̄ = p`
  have heq : σ tb = p := hcaus htbp (h3' tb htb)
  rcases htb.1.eq_or_lt with h | h
  · subst h; exact h2 heq
  · exact d.not_mem (heq ▸ hσW tb ⟨h, htb.2⟩)

end PastBoundaryChartData

/-! ### (A) alone -/

/-- **(A) alone excludes a past boundary chart, in a locally closed, antisymmetric ambient.** Let
`U` be an open set containing `W` and `Ũ`, with `≤_U` closed in `U × U` and antisymmetric, on a
T2 space. If `W` satisfies (A) of `not_pastBoundaryChart_of_flrwType`, then `Ũ` is not a past
boundary chart of `W` at any point. Proof: (A) is applied to `γ̃` and to the curve `σ` of field
(vi) at the closure of the chart diamond, both past-inextensible in `W` over `(0, 1]` (step (a)).
Then `σ t ∈ W = ⋃ I⁺(γ̃ s, W)` gives (3), `γ̃ s ∈ W = ⋃ I⁺(σ t, W)` gives (4), and
`false_of_squeeze` closes. -/
theorem not_pastBoundaryChart_of_flrwTypeA_of_closedIn [T2Space M] {U : Opens M} (hWU : W ≤ U)
    (hŨU : Ũ ≤ U)
    (hcl : closure {z : M × M | C.le U z.1 z.2} ∩ ((U : Set M) ×ˢ (U : Set M)) ⊆
      {z : M × M | C.le U z.1 z.2})
    (hcaus : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iplus W {γ t} = W)
    (p : M) : ¬ C.PastBoundaryChart W Ũ p := by
  rintro ⟨d⟩
  have hVW : d.inside ≤ W := d.inside_le.trans inf_le_left
  have h1 : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  -- (vi) at the closure of the chart diamond, compact in `Ũ` by (v)
  obtain ⟨σ, hσ, hσ0, hσmem, -⟩ := d.avoid _ d.isCompact_closure d.closure_subset
  -- step (a): `γ̃` and `σ` are past-inextensible chronal curves of `W` over `(0, 1]`
  obtain ⟨hγinex, hγchr⟩ := ChronalCurveOn.pastInextensible_Ioc_of_start_notMem d.chronalCurveOn
    h1 (fun t ht => hVW (d.curve_mem t ht)) (by rw [d.curve_zero]; exact d.not_mem)
  obtain ⟨hσinex, hσchr⟩ := ChronalCurveOn.pastInextensible_Ioc_of_start_notMem hσ h1
    (fun t ht => hVW (hσmem t ht).1) hσ0
  -- (A), twice
  have hγA := hA _ _ hγinex hγchr
  have hσA := hA _ _ hσinex hσchr
  refine d.false_of_squeeze hŨU hcl hcaus hσ (fun t ht => hVW (hσmem t ht).1)
    (fun t ht hK => (hσmem t ht).2 (subset_closure hK)) (fun t ht => ?_) (fun s hs => ?_)
  · -- (3): `σ t ∈ W = ⋃ I⁺(γ̃ s, W)` and `p ≪_Ũ γ̃ s`
    have hx : σ t ∈ (W : Set M) := hVW (hσmem t ht).1
    rw [← hγA] at hx
    obtain ⟨s, hs, hst⟩ := mem_iUnion₂.1 hx
    have hps : C.lt Ũ p (d.curve s) := by
      have := d.chronalCurveOn.lt_of_lt le_rfl hs.1 hs.2
      rwa [d.curve_zero] at this
    exact C.le_of_lt (C.lt_trans (C.lt_mono hŨU hps)
      (C.lt_mono hWU (Precausality.mem_Iplus_singleton.1 hst)))
  · -- (4): `γ̃ s ∈ W = ⋃ I⁺(σ t, W)`
    have hx : d.curve s ∈ (W : Set M) := hVW (d.curve_mem s hs)
    rw [← hσA] at hx
    obtain ⟨t, ht, hts⟩ := mem_iUnion₂.1 hx
    exact ⟨t, ht, C.le_of_lt (C.lt_mono hWU (Precausality.mem_Iplus_singleton.1 hts))⟩

/-- **The theorem: in a closed, antisymmetric ambient, (A) alone excludes a past boundary
chart.** On a T2 space with `{z | z.1 ≤_M z.2}` closed and `≤_M` antisymmetric, an open `W`
satisfying (A) of `not_pastBoundaryChart_of_flrwType` has a past boundary chart at no point. There
is no (B), no future one-connectedness, no causal arc-connectedness and no second countability.
It is `not_pastBoundaryChart_of_flrwTypeA_of_closedIn` at `U = ⊤`. -/
theorem not_pastBoundaryChart_of_flrwTypeA_of_isClosed_le [T2Space M]
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) (hcaus : C.IsCausal)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iplus W {γ t} = W)
    (Ũ : Opens M) (p : M) : ¬ C.PastBoundaryChart W Ũ p :=
  not_pastBoundaryChart_of_flrwTypeA_of_closedIn le_top le_top
    (fun _ hz => hle.closure_subset hz.1) hcaus hA p

/-- **The corollary: on every globally hyperbolic, tarentin T2 spacetime**, an open `W` with (A)
has a past boundary chart at no point. `≤` is closed by `GloballyHyperbolic.isClosed_le`, and
`GloballyHyperbolic` includes `IsCausal`. Minkowski space is among these spacetimes
(`minkowski_isCausal`, `minkowski_tarentin`, `minkowski_globallyHyperbolic`,
`Causal/Minkowski.lean:110, :121, :132`), but that application is layer 3 and is not stated here.
It covers every open set of `𝐌^{1+n}` with (A), not only the half-space. -/
theorem GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeA [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iplus W {γ t} = W)
    (Ũ : Opens M) (p : M) : ¬ C.PastBoundaryChart W Ũ p :=
  not_pastBoundaryChart_of_flrwTypeA_of_isClosed_le (hG.isClosed_le hT) hG.1 hA Ũ p

/-- **The instance check: a past boundary chart forces (A) to fail**, on a globally hyperbolic,
tarentin T2 spacetime. This is the contrapositive of the corollary. At the half-space
`W = {t > 0}` of `𝐌^{1+n}`, `n ≥ 1`, which has a chart at `0` (`minkowski_pastBoundaryChart`,
`Causal.Model.MinkowskiPastBoundaryChart`, layer 3), it gives ¬(A). That is
`minkowski_posHalfSpace_not_flrwTypeA`, here by closedness and antisymmetry instead of the explicit
point `(1, e) ∉ I⁺(0)`. The application is checked in the target's `Probe.lean`, which imports the
model; this module does not. -/
theorem GloballyHyperbolic.not_flrwTypeA_of_pastBoundaryChart [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (h : C.PastBoundaryChart W Ũ p) :
    ¬ ∀ (I : Set ℝ) (γ : ℝ → M), C.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iplus W {γ t} = W :=
  fun hA => hG.not_pastBoundaryChart_of_flrwTypeA hT hA Ũ p h

/-! ### The time reversal -/

/-- **(A) for future-inextensible curves is (A) for the reversed causality**: if every
future-inextensible chronal curve of `W` has chronological past `W`, then every past-inextensible
chronal curve of `W` for `C.dual` has chronological future `W` for `C.dual`. This is the
conversion inside `not_futureBoundaryChart_of_flrwType` (`FlrwType.lean:364–378`). -/
theorem dual_iUnion_Iplus_eq_of_futureInextensible
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.FutureInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iminus W {γ t} = W) :
    ∀ (I : Set ℝ) (γ : ℝ → M), C.dual.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.dual.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.dual.Iplus W {γ t} = W := by
  intro I γ hγ hchr
  have h1 : C.FutureInextensible W (-I) (fun t => γ (-t)) := by
    have := (dual_pastInextensible_iff (C := C) (W := W) (I := -I) (c := fun t => γ (-t))).1
    simp only [neg_neg] at this
    exact this hγ
  have h2 : ∀ a ∈ -I, ∀ b ∈ -I, C.ChronalCurveOn W (fun t => γ (-t)) a b := fun a ha b hb =>
    CurveOn.neg (hchr (-b) hb (-a) ha)
  rw [← hA (-I) _ h1 h2]
  ext x
  simp only [mem_iUnion, exists_prop, Set.mem_neg]
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨-t, by rwa [neg_neg], by rw [neg_neg]; exact hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨-t, ht, hx⟩

/-- **The time reversal, local form**: no future boundary chart, under (A) for future-inextensible
curves and their chronological pasts, when `≤_U` is closed in `U × U` and antisymmetric for an
open `U ≥ W ⊔ Ũ`. It is the past form for `C.dual`: `≤` reversed is closed and antisymmetric. -/
theorem not_futureBoundaryChart_of_flrwTypeA_of_closedIn [T2Space M] {U : Opens M} (hWU : W ≤ U)
    (hŨU : Ũ ≤ U)
    (hcl : closure {z : M × M | C.le U z.1 z.2} ∩ ((U : Set M) ×ˢ (U : Set M)) ⊆
      {z : M × M | C.le U z.1 z.2})
    (hcaus : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.FutureInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iminus W {γ t} = W)
    (p : M) : ¬ C.FutureBoundaryChart W Ũ p :=
  not_pastBoundaryChart_of_flrwTypeA_of_closedIn (C := C.dual) hWU hŨU
    (fun _ hz => hcl ⟨continuous_swap.closure_preimage_subset {z : M × M | C.le U z.1 z.2} hz.1,
      hz.2.2, hz.2.1⟩)
    (fun _ _ h1 h2 => hcaus h2 h1) (dual_iUnion_Iplus_eq_of_futureInextensible hA) p

/-- **The time reversal**: in a closed, antisymmetric T2 ambient, an open `W` with (A) for
future-inextensible curves and their chronological pasts has a future boundary chart at no
point. -/
theorem not_futureBoundaryChart_of_flrwTypeA_of_isClosed_le [T2Space M]
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) (hcaus : C.IsCausal)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.FutureInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iminus W {γ t} = W)
    (Ũ : Opens M) (p : M) : ¬ C.FutureBoundaryChart W Ũ p :=
  not_futureBoundaryChart_of_flrwTypeA_of_closedIn le_top le_top
    (fun _ hz => hle.closure_subset hz.1) hcaus hA p

/-- **The time reversal on every globally hyperbolic, tarentin T2 spacetime.** -/
theorem GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeA [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic)
    (hA : ∀ (I : Set ℝ) (γ : ℝ → M), C.FutureInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iminus W {γ t} = W)
    (Ũ : Opens M) (p : M) : ¬ C.FutureBoundaryChart W Ũ p :=
  not_futureBoundaryChart_of_flrwTypeA_of_isClosed_le (hG.isClosed_le hT) hG.1 hA Ũ p

/-! ### (B) alone (the optional report, proved) -/

/-- **(B) alone excludes a past boundary chart, in a locally closed, antisymmetric ambient.** Let
`M` be T2 and second countable, `W` causally arc-connected, and `U` an open set containing `W` and
`Ũ`, with `≤_U` closed in `U × U` and antisymmetric. If `W` satisfies (B) of
`not_pastBoundaryChart_of_flrwType`, then `Ũ` is not a past boundary chart of `W` at any point.
Proof: `γ̃` and `σ` (field (vi) at the closure of the diamond) are past-inextensible in `W` over
`(0, 1]`. For (3), take (B) at `σ t`, which gives `S ⊆ I⁻(σ t, W)`. If `γ̃ 1 ∈ J⁺(S, W)`, then
`γ̃` meets `S` by `(2.4)` (`PastInextensible.exists_mem_of_mem_Jplus`). Otherwise
`γ̃ 1 ∈ J⁻(S, W)`, by the split. Either way `p ≤_U σ t`. (4) is the same argument at `γ̃ s`, with
`σ` in place of `γ̃`. `false_of_squeeze` closes. Unlike `not_pastBoundaryChart_of_flrwType`, this
uses no (A), no future one-connectedness, no field (iii) and no `γ̃ 1 ≪_Ũ σ 1`. -/
theorem not_pastBoundaryChart_of_flrwTypeB_of_closedIn [T2Space M] [SecondCountableTopology M]
    {U : Opens M} (hWU : W ≤ U) (hŨU : Ũ ≤ U)
    (hcl : closure {z : M × M | C.le U z.1 z.2} ∩ ((U : Set M) ×ˢ (U : Set M)) ⊆
      {z : M × M | C.le U z.1 z.2})
    (hcaus : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y)
    (hcac : C.CausallyArcConnectedOn W)
    (hB : ∀ x ∈ W, ∃ S : Set M, C.IsCauchySurfaceOn W S ∧ S ⊆ C.Iminus W {x})
    (p : M) : ¬ C.PastBoundaryChart W Ũ p := by
  rintro ⟨d⟩
  have hVW : d.inside ≤ W := d.inside_le.trans inf_le_left
  have h1 : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  have hcausW : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y := fun _ _ hxy hyx =>
    hcaus (C.le_mono hWU hxy) (C.le_mono hWU hyx)
  -- (vi) at the closure of the chart diamond, compact in `Ũ` by (v)
  obtain ⟨σ, hσ, hσ0, hσmem, -⟩ := d.avoid _ d.isCompact_closure d.closure_subset
  -- step (a): `γ̃` and `σ` are past-inextensible in `W` over `(0, 1]`
  have hγinex := (ChronalCurveOn.pastInextensible_Ioc_of_start_notMem d.chronalCurveOn
    h1 (fun t ht => hVW (d.curve_mem t ht)) (by rw [d.curve_zero]; exact d.not_mem)).1
  have hσinex := (ChronalCurveOn.pastInextensible_Ioc_of_start_notMem hσ h1
    (fun t ht => hVW (hσmem t ht).1) hσ0).1
  refine d.false_of_squeeze hŨU hcl hcaus hσ (fun t ht => hVW (hσmem t ht).1)
    (fun t ht hK => (hσmem t ht).2 (subset_closure hK)) (fun t ht => ?_) (fun s hs => ?_)
  · -- (3): (B) at `σ t`; `γ̃ 1` is above `S` (then `γ̃` meets `S`, (2.4)) or below it
    obtain ⟨S, hS, hSσ⟩ := hB _ (hVW (hσmem t ht).1)
    have hp1 : C.lt Ũ p (d.curve 1) := by
      have := d.chronalCurveOn.lt_of_lt le_rfl zero_lt_one le_rfl
      rwa [d.curve_zero] at this
    rcases hS.mem_Jplus_union_Jminus (hVW (d.curve_mem 1 h1)) with h | ⟨z, hz, h1z⟩
    · obtain ⟨u, hu, huS⟩ := hγinex.exists_mem_of_mem_Jplus hS hcac hcausW ⟨1, h1, h⟩
      have hpu : C.lt Ũ p (d.curve u) := by
        have := d.chronalCurveOn.lt_of_lt le_rfl hu.1 hu.2
        rwa [d.curve_zero] at this
      exact C.le_of_lt (C.lt_trans (C.lt_mono hŨU hpu)
        (C.lt_mono hWU (Precausality.mem_Iminus_singleton.1 (hSσ huS))))
    · exact C.le_trans (C.le_of_lt (C.lt_mono hŨU hp1)) (C.le_trans (C.le_mono hWU h1z)
        (C.le_of_lt (C.lt_mono hWU (Precausality.mem_Iminus_singleton.1 (hSσ hz)))))
  · -- (4): (B) at `γ̃ s`; `σ 1` is above `S` (then `σ` meets `S`, (2.4)) or below it
    obtain ⟨S, hS, hSγ⟩ := hB _ (hVW (d.curve_mem s hs))
    rcases hS.mem_Jplus_union_Jminus (hVW (hσmem 1 h1).1) with h | ⟨z, hz, h1z⟩
    · obtain ⟨t, ht, htS⟩ := hσinex.exists_mem_of_mem_Jplus hS hcac hcausW ⟨1, h1, h⟩
      exact ⟨t, ht, C.le_of_lt (C.lt_mono hWU (Precausality.mem_Iminus_singleton.1 (hSγ htS)))⟩
    · exact ⟨1, h1, C.le_trans (C.le_mono hWU h1z)
        (C.le_of_lt (C.lt_mono hWU (Precausality.mem_Iminus_singleton.1 (hSγ hz))))⟩

/-- **In a closed, antisymmetric ambient, (B) alone excludes a past boundary chart**, on a T2,
second countable space, for a causally arc-connected `W`. It is
`not_pastBoundaryChart_of_flrwTypeB_of_closedIn` at `U = ⊤`. -/
theorem not_pastBoundaryChart_of_flrwTypeB_of_isClosed_le [T2Space M] [SecondCountableTopology M]
    (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) (hcaus : C.IsCausal)
    (hcac : C.CausallyArcConnectedOn W)
    (hB : ∀ x ∈ W, ∃ S : Set M, C.IsCauchySurfaceOn W S ∧ S ⊆ C.Iminus W {x})
    (Ũ : Opens M) (p : M) : ¬ C.PastBoundaryChart W Ũ p :=
  not_pastBoundaryChart_of_flrwTypeB_of_closedIn le_top le_top
    (fun _ hz => hle.closure_subset hz.1) hcaus hcac hB p

/-- **(B) alone, on every globally hyperbolic, tarentin T2, second countable spacetime**, for a
causally arc-connected `W`. -/
theorem GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeB [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hcac : C.CausallyArcConnectedOn W)
    (hB : ∀ x ∈ W, ∃ S : Set M, C.IsCauchySurfaceOn W S ∧ S ⊆ C.Iminus W {x})
    (Ũ : Opens M) (p : M) : ¬ C.PastBoundaryChart W Ũ p :=
  not_pastBoundaryChart_of_flrwTypeB_of_isClosed_le (hG.isClosed_le hT) hG.1 hcac hB Ũ p

/-- **A past boundary chart forces (B) to fail**, on a globally hyperbolic, tarentin T2, second
countable spacetime, for a causally arc-connected `W`. At the half-space of `𝐌^{1+n}`, `n ≥ 1`,
which is causally arc-connected (`minkowski_posHalfSpace_flrwType_check`), it gives
`minkowski_posHalfSpace_not_flrwTypeB` (layer 3; checked in the target's `Probe.lean`). -/
theorem GloballyHyperbolic.not_flrwTypeB_of_pastBoundaryChart [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hcac : C.CausallyArcConnectedOn W) (h : C.PastBoundaryChart W Ũ p) :
    ¬ ∀ x ∈ W, ∃ S : Set M, C.IsCauchySurfaceOn W S ∧ S ⊆ C.Iminus W {x} :=
  fun hB => hG.not_pastBoundaryChart_of_flrwTypeB hT hcac hB Ũ p h

/-- **(B) alone, time reversal, local form**: no future boundary chart, under (B) with
`S ⊆ I⁺(x, W)`, for a causally arc-connected `W` on a T2, second countable space, when `≤_U` is
closed in `U × U` and antisymmetric for an open `U ≥ W ⊔ Ũ`. It is the past form for `C.dual`. -/
theorem not_futureBoundaryChart_of_flrwTypeB_of_closedIn [T2Space M] [SecondCountableTopology M]
    {U : Opens M} (hWU : W ≤ U) (hŨU : Ũ ≤ U)
    (hcl : closure {z : M × M | C.le U z.1 z.2} ∩ ((U : Set M) ×ˢ (U : Set M)) ⊆
      {z : M × M | C.le U z.1 z.2})
    (hcaus : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y)
    (hcac : C.CausallyArcConnectedOn W)
    (hB : ∀ x ∈ W, ∃ S : Set M, C.IsCauchySurfaceOn W S ∧ S ⊆ C.Iplus W {x})
    (p : M) : ¬ C.FutureBoundaryChart W Ũ p :=
  not_pastBoundaryChart_of_flrwTypeB_of_closedIn (C := C.dual) hWU hŨU
    (fun _ hz => hcl ⟨continuous_swap.closure_preimage_subset {z : M × M | C.le U z.1 z.2} hz.1,
      hz.2.2, hz.2.1⟩)
    (fun _ _ h1 h2 => hcaus h2 h1) (dual_causallyArcConnectedOn.2 hcac)
    (fun x hx => let ⟨S, hS, hSx⟩ := hB x hx; ⟨S, dual_isCauchySurfaceOn.2 hS, hSx⟩) p

/-- **(B) alone, time reversal**: in a closed, antisymmetric T2, second countable ambient, a
causally arc-connected `W` every `I⁺(x, W)` of which contains a Cauchy surface of `W` has a
future boundary chart at no point. -/
theorem not_futureBoundaryChart_of_flrwTypeB_of_isClosed_le [T2Space M]
    [SecondCountableTopology M] (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) (hcaus : C.IsCausal)
    (hcac : C.CausallyArcConnectedOn W)
    (hB : ∀ x ∈ W, ∃ S : Set M, C.IsCauchySurfaceOn W S ∧ S ⊆ C.Iplus W {x})
    (Ũ : Opens M) (p : M) : ¬ C.FutureBoundaryChart W Ũ p :=
  not_futureBoundaryChart_of_flrwTypeB_of_closedIn le_top le_top
    (fun _ hz => hle.closure_subset hz.1) hcaus hcac hB p

end Causality

/-! ### Witnesses on the timelike line (kb/0011) -/

open Causality

/-- **The (A)-theorem applies on the timelike line.** `W = (0, ∞)` satisfies (A)
(`timelikeLine_flrwType_hypotheses_posHalfLine`), and the timelike line is globally hyperbolic and
tarentin, so `W` has no past boundary chart, by
`GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeA`. This agrees with
`timelikeLine_not_pastBoundaryChart`, which proves it for every open set by a one-dimensional
argument. -/
theorem timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeA (Ũ : Opens ℝ) (p : ℝ) :
    ¬ timelikeLine.PastBoundaryChart posHalfLine Ũ p :=
  timelikeLine_globallyHyperbolic.not_pastBoundaryChart_of_flrwTypeA timelikeLine_tarentin
    timelikeLine_flrwType_hypotheses_posHalfLine.2.2.2.1 Ũ p

/-- **The (B)-theorem applies on the timelike line.** `W = (0, ∞)` is causally arc-connected and
satisfies (B) (`timelikeLine_flrwType_hypotheses_posHalfLine`), so it has no past boundary chart,
by `GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeB`. -/
theorem timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeB (Ũ : Opens ℝ) (p : ℝ) :
    ¬ timelikeLine.PastBoundaryChart posHalfLine Ũ p :=
  timelikeLine_globallyHyperbolic.not_pastBoundaryChart_of_flrwTypeB timelikeLine_tarentin
    timelikeLine_flrwType_hypotheses_posHalfLine.1
    timelikeLine_flrwType_hypotheses_posHalfLine.2.2.2.2 Ũ p

end Causal
