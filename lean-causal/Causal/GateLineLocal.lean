import Causal.CBG.CausalConvex
import Causal.LadderLocal

/-!
# The gated line's local facts: locally push-up and not push-up; causally open in the future, locally causally open on both sides, and not causally open in the past

Programme target `T-abs-gateline-local` (`programme/roadmap.toml:632`; layer 1, no label of
`ETT.tex`; ETT-layer imports only, no model, no metric notion). The gated line `Causal.gateLine`
(`Causal/CBG/CausalConvex.lean:842`) is the timelike line on `ℝ ⊕ Unit` plus an isolated point
`⋆ = inr ()`: `inl a ≤_U inl b` iff `a ≤ b` and `[a, b] ⊆ U`; `inl a ≤_U ⋆` iff `a ≤ 10` and
`inl a, ⋆, inl 5 ∈ U`; `⋆ ≤_U ⋆` iff `⋆ ∈ U`; `≪` only on the line.

**`T-abs-gateline-local/1-locally-push-up`** — `gateLine_locallyPushUp`; its local form
`gateLine_pushUpOn` (push-up on every open missing `⋆` or the gate `inl 5`).
**`T-abs-gateline-local/2-not-push-up`** — `gateLine_not_pushUp` (`0 ≪ 1 ≤ ⋆`, nothing `≪ ⋆`).
**`T-abs-gateline-local/3-causally-open-future`** — `gateLine_causallyOpenFuture`, through
`gateLine_preimage_inl_Jplus` (the line part of `J⁺_U(A)` is the timelike line's).
**`T-abs-gateline-local/4-not-causally-open`** — `gateLine_Jminus_star`
(`J⁻_M(⋆) = (−∞, 10] ∪ {⋆}`), `gateLine_not_isOpen_Jminus_star`, `gateLine_not_causallyOpen`,
`gateLine_not_causallyOpenPast`.
**`T-abs-gateline-local/5-locally-causally-open`** — `gateLine_locallyCausallyOpen`; its local
form `gateLine_isOpen_Jminus` (`J⁻_U(V)` open whenever `U` misses `⋆` or the gate).
**`T-abs-gateline-local/6-separations`** — `gateLine_separates_causallyOpen` (the printed `J⁺`
form of `def:causally_open_spacetime_open` is strictly weaker than DEC-8's two-sided reading,
with global hyperbolicity, strong causality, curves extending, local push-up and two-sided local
causal openness, and without absolute minimality), `gateLine_separates_pushUp` (local push-up and
the rest, without causal arc-connectedness and without push-up).
Beyond the target: the gated line is strongly causal, both forms (`gateLine_stronglyCausalOpen`,
`gateLine_stronglyCausal`), conjoined into both separations.

> Let $M$ be a topological spacetime. The causality of $M$ is open, and $M$ is causally open, if
> for every open subset $\U$ of $M$ and every open subset $\V\subset \U$ the set $J^+_\U(\V)$ is
> open. (`def:causally_open_spacetime_open`, `ETT.tex:694–697`; read with `J^±` by DEC-8)

> Let $M$ be a causally arc-connected topological spacetime and let $(\U_i)_{i\in I}$ be a cover
> of $M$ by open subsets each having the push-up property. Then $M$ has the push-up property.
> (`lem:pushup_local`, `ETT.tex:557–560`)

> If $M$ is absolutely minimal and if for every $p\in M$ there exists a neighbourhood $\U$ of $p$
> whose causality is open, then the causality of $M$ is open.
> (`prop:topological_spacetime_absolutely_minimal`, `ETT.tex:698–701`)

> The gated line's local facts: locally push-up and not push-up (0 ≪ 1 ≤ ⋆, nothing ≪ ⋆),
> two-sided locally causally open, causally open in the future and NOT causally open in the past
> (J⁻({⋆}) = (−∞, 10] ∪ {⋆} is not open), so that the printed J⁺-only causal openness is strictly
> weaker than DEC-8's two-sided reading — proved, or refuted by a counterexample
> (`programme/roadmap.toml:633`)

## Hypothesis checklist

| target claim | here |
|---|---|
| locally push-up: `{⋆}` and the line are opens with push-up | ✓ proved, more generally on every open missing `⋆` or the gate (`gateLine_pushUpOn`) |
| not push-up: `0 ≪ 1 ≤ ⋆`, nothing `≪ ⋆` | ✓ proved at `U = ⊤` |
| causally open in the future: `J⁺_U(V)` is its line part, open as on the timelike line, plus possibly `⋆` | ✓ proved, the line part being exactly the timelike line's `J⁺` (`gateLine_preimage_inl_Jplus`) |
| two-sided locally causally open | ✓ proved, with the line as neighbourhood of `inl a` and `{⋆}` of `⋆`; past side on every open missing `⋆` or the gate |
| not causally open in the past: `J⁻({⋆}) = (−∞, 10] ∪ {⋆}` not open | ✓ proved, with `V = {⋆}` open and `U = ⊤` |

## SCOPE (disclosed)

* **The outcome, as a finding**: the gated line has `CausallyOpenFuture`
  (`def:causally_open_spacetime_open` as printed) and not `CausallyOpen` (DEC-8's reading), so the
  printed definition is strictly weaker than the definition of record — in the library's reading of
  `defi:causalite` without gluing (kb/0014; OQ-18 is open), since the gated line is not absolutely
  minimal; the gap sits at one
  point, the isolated `⋆`, whose past `J⁻_M(⋆) = (−∞, 10] ∪ {⋆}` has the closed end `10`. The
  keeper's argument (`programme/roadmap.toml:642`) is confirmed in every part; nothing was
  refuted.
* **The first non-implication needs a non-local causality.** The gated line is not absolutely minimal
  (`gateLine_not_absolutelyMinimalOn`) and not causally arc-connected
  (`gateLine_cauchyInclusion_not_causallyConvex`, fifth conjunct): with absolute minimality,
  local two-sided causal openness gives causal openness
  (`AbsolutelyMinimal.causallyOpen_of_locallyCausallyOpen`), and with causal arc-connectedness
  local push-up gives push-up (`lem:pushup_local`). The separations say that neither hypothesis
  can be dropped. For causal openness they say nothing about a local causality (kb/0019); for
  push-up, a witness must fail arc-connectedness, and whether absolute minimality plus local push-up
  gives push-up on a T1 space is argued (an auditor's sketch), not in Lean.
* **The opens chosen are the large ones**: push-up and past causal openness hold on every open
  missing `⋆` or the gate `inl 5` (`gateLine_pushUpOn`, `gateLine_isOpen_Jminus`). Both fail on
  `⊤`; which other opens containing both `⋆` and the gate they fail on is not stated.
* **No separation, no countability is used**; `ℝ ⊕ Unit` is Hausdorff and second countable
  (mathlib instances), one of ETT's spacetimes, so the separations are ladder `[[fails]]` with
  the ambient space. Time functions and tarentin of the gated line are
  `T-abs-gateline-witnesses`'s, in another module; not stated here.
* **Strong causality is beyond the target** (not in its `uses`): stated because it is cheap — a
  segment of the line and `{⋆}` are causally convex in `M` — and it adds `strongly_causal(_open)`
  to the `from` of each separation.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Sum

/-- The trace of an open set of the gated line on the line, as an open set of `ℝ`. -/
def gateLineTrace (U : Opens (ℝ ⊕ Unit)) : Opens ℝ :=
  ⟨inl ⁻¹' (U : Set (ℝ ⊕ Unit)), U.isOpen.preimage continuous_inl⟩

/-- The line of the gated line, as an open set. -/
def gateLineLine : Opens (ℝ ⊕ Unit) := ⟨range inl, isOpen_range_inl⟩

variable {U V W : Opens (ℝ ⊕ Unit)}

/-! ## Push-up: local, not global -/

/-- **Push-up on every open missing `⋆` or the gate**: the only failure of push-up is
`x ≪_U y ≤_U ⋆`, and `y ≤_U ⋆` needs `⋆` and `inl 5` in `U`. -/
theorem gateLine_pushUpOn
    (hW : (inr () : ℝ ⊕ Unit) ∉ W ∨ (inl 5 : ℝ ⊕ Unit) ∉ W) : gateLine.PushUpOn W := by
  intro U hUW x y z
  refine ⟨fun hxy hyz => ?_, fun hxy hyz => ?_⟩
  · rcases x with a | ⟨⟩ <;> rcases y with b | ⟨⟩
    · rcases z with c | ⟨⟩
      · exact ⟨hxy.1.trans_le hyz.1, Icc_subset_Icc_union_Icc.trans (union_subset hxy.2 hyz.2)⟩
      · exfalso
        rcases hW with h | h
        · exact h (hUW hyz.2.2.1)
        · exact h (hUW hyz.2.2.2)
    all_goals exact hxy.elim
  · rcases y with b | ⟨⟩ <;> rcases z with c | ⟨⟩
    · rcases x with a | ⟨⟩
      · exact ⟨hxy.1.trans_lt hyz.1, Icc_subset_Icc_union_Icc.trans (union_subset hxy.2 hyz.2)⟩
      · exact hxy.elim
    all_goals exact hyz.elim

/-- **The gated line has local push-up** (`locally_push_up`): the line and `{⋆}` are open
neighbourhoods with push-up. -/
theorem gateLine_locallyPushUp : gateLine.LocallyPushUp := by
  rintro (a | ⟨⟩)
  · refine ⟨gateLineLine, ⟨a, rfl⟩, gateLine_pushUpOn (Or.inl fun h => ?_)⟩
    obtain ⟨b, hb⟩ := h
    exact inl_ne_inr hb
  · refine ⟨gateStar, ⟨(), rfl⟩, gateLine_pushUpOn (Or.inr fun h => ?_)⟩
    obtain ⟨u, hu⟩ := h
    exact inr_ne_inl hu

/-- **The gated line has not push-up**: `0 ≪ 1 ≤ ⋆` in `M`, but nothing is `≪ ⋆`. -/
theorem gateLine_not_pushUp : ¬ gateLine.PushUp := by
  intro h
  have h₁ : gateLine.lt ⊤ (inl 0 : ℝ ⊕ Unit) (inl 1) := ⟨zero_lt_one, fun _ _ => trivial⟩
  have h₂ : gateLine.le ⊤ (inl 1 : ℝ ⊕ Unit) (inr ()) := ⟨by norm_num, trivial, trivial, trivial⟩
  exact (h.lt_of_lt_of_le h₁ h₂).elim

/-! ## Causal openness in the future -/

/-- **The line part of `J⁺_U(A)` is the timelike line's** `J⁺` of the traces: `⋆` is in nobody's
past on the line. -/
theorem gateLine_preimage_inl_Jplus (U : Opens (ℝ ⊕ Unit)) (A : Set (ℝ ⊕ Unit)) :
    inl ⁻¹' gateLine.Jplus U A = timelikeLine.Jplus (gateLineTrace U) (inl ⁻¹' A) := by
  ext b
  constructor
  · rintro ⟨x, hx, hxb⟩
    rcases x with a | ⟨⟩
    · exact ⟨a, hx, hxb⟩
    · exact hxb.elim
  · rintro ⟨a, ha, hab⟩
    exact ⟨inl a, ha, hab⟩

/-- `J⁺_U(V)` is open for every open `V ≤ U`: its line part is open as on the timelike line, and
`⋆` is isolated. -/
theorem gateLine_isOpen_Jplus (hVU : V ≤ U) : IsOpen (gateLine.Jplus U V) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, isOpen_discrete _⟩
  rw [gateLine_preimage_inl_Jplus]
  exact timelikeLine_causallyOpen_of_chronalNeighbours.1 (gateLineTrace U) (gateLineTrace V)
    fun _ hx => hVU hx

/-- **The gated line is causally open in the future** (`causally_open_future`,
`def:causally_open_spacetime_open` as printed). -/
theorem gateLine_causallyOpenFuture : gateLine.CausallyOpenFuture :=
  fun _ _ hVU => gateLine_isOpen_Jplus hVU

/-! ## Causal openness in the past: local, not global -/

/-- **The line part of `J⁻_U(A)` is the timelike line's**, when `U` misses `⋆` or the gate. -/
theorem gateLine_preimage_inl_Jminus
    (hU : (inr () : ℝ ⊕ Unit) ∉ U ∨ (inl 5 : ℝ ⊕ Unit) ∉ U) (A : Set (ℝ ⊕ Unit)) :
    inl ⁻¹' gateLine.Jminus U A = timelikeLine.Jminus (gateLineTrace U) (inl ⁻¹' A) := by
  ext a
  constructor
  · rintro ⟨x, hx, hax⟩
    rcases x with b | ⟨⟩
    · exact ⟨b, hx, hax⟩
    · exfalso
      rcases hU with h | h
      · exact h hax.2.2.1
      · exact h hax.2.2.2
  · rintro ⟨b, hb, hab⟩
    exact ⟨inl b, hb, hab⟩

/-- `J⁻_U(V)` is open for every open `V ≤ U`, when `U` misses `⋆` or the gate. -/
theorem gateLine_isOpen_Jminus
    (hU : (inr () : ℝ ⊕ Unit) ∉ U ∨ (inl 5 : ℝ ⊕ Unit) ∉ U) (hVU : V ≤ U) :
    IsOpen (gateLine.Jminus U V) := by
  rw [isOpen_sum_iff]
  refine ⟨?_, isOpen_discrete _⟩
  rw [gateLine_preimage_inl_Jminus hU]
  exact timelikeLine_causallyOpen_of_chronalNeighbours.2 (gateLineTrace U) (gateLineTrace V)
    fun _ hx => hVU hx

/-- **The gated line is locally causally open, on both sides** (`locally_causally_open`, DEC-8):
the line is a neighbourhood of `inl a`, `{⋆}` one of `⋆`. -/
theorem gateLine_locallyCausallyOpen : gateLine.LocallyCausallyOpen := by
  rw [Causality.locallyCausallyOpen_iff]
  rintro (a | ⟨⟩)
  · refine ⟨gateLineLine, ⟨a, rfl⟩, fun _ _ _ hVU => gateLine_isOpen_Jplus hVU,
      fun U _ hU hVU => gateLine_isOpen_Jminus (Or.inl fun h => ?_) hVU⟩
    obtain ⟨b, hb⟩ := hU h
    exact inl_ne_inr hb
  · refine ⟨gateStar, ⟨(), rfl⟩, fun _ _ _ hVU => gateLine_isOpen_Jplus hVU,
      fun U _ hU hVU => gateLine_isOpen_Jminus (Or.inr fun h => ?_) hVU⟩
    obtain ⟨u, hu⟩ := hU h
    exact inr_ne_inl hu

/-- **The causal past of `⋆`**: `J⁻_M(⋆) = (−∞, 10] ∪ {⋆}`. -/
theorem gateLine_Jminus_star :
    gateLine.Jminus ⊤ {inr ()} = inl '' Iic (10 : ℝ) ∪ {inr ()} := by
  ext x
  rw [Precausality.mem_Jminus_singleton]
  rcases x with a | ⟨⟩
  · simp
  · simp

/-- **`J⁻_M({⋆})` is not open**, `{⋆}` being open: its line part `(−∞, 10]` is not. -/
theorem gateLine_not_isOpen_Jminus_star :
    ¬ IsOpen (gateLine.Jminus ⊤ (gateStar : Set (ℝ ⊕ Unit))) := by
  intro h
  have hstar : (gateStar : Set (ℝ ⊕ Unit)) = {inr ()} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      rfl
    · rintro rfl
      exact ⟨(), rfl⟩
  rw [hstar, gateLine_Jminus_star] at h
  have h' := h.preimage continuous_inl
  have hpre : inl ⁻¹' (inl '' Iic (10 : ℝ) ∪ {inr ()} : Set (ℝ ⊕ Unit)) = Iic 10 := by
    ext a
    simp
  rw [hpre] at h'
  rcases isClopen_iff.1 ⟨isClosed_Iic, h'⟩ with h0 | h1
  · have h10 : (10 : ℝ) ∈ Iic (10 : ℝ) := self_mem_Iic
    rw [h0] at h10
    exact h10
  · have h11 : (11 : ℝ) ∈ Iic (10 : ℝ) := h1 ▸ mem_univ _
    norm_num at h11

/-- **The gated line is not causally open in the past**: `C.dual` is not causally open in the
future. -/
theorem gateLine_not_causallyOpenPast : ¬ gateLine.dual.CausallyOpenFuture := fun h =>
  gateLine_not_isOpen_Jminus_star (h ⊤ gateStar le_top)

/-- **The gated line is not causally open** in DEC-8's reading (`causally_open`). -/
theorem gateLine_not_causallyOpen : ¬ gateLine.CausallyOpen := fun h =>
  gateLine_not_isOpen_Jminus_star (h.2 ⊤ gateStar le_top)

/-! ## Beyond the target: strong causality -/

/-- **The gated line is strongly causal, open form** (`strongly_causal_open`): a segment of the
line, or `{⋆}`, is causally convex in `M`; nothing lies between two points of the line but the
segment between them (`⋆` precedes nothing on the line), and nothing is above `⋆` but `⋆`. -/
theorem gateLine_stronglyCausalOpen : gateLine.StronglyCausalOpen := by
  rintro (a | ⟨⟩) N hN
  · have hN' : inl ⁻¹' N ∈ 𝓝 a := continuous_inl.continuousAt.preimage_mem_nhds hN
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN'
    refine ⟨⟨inl '' Ioo l u, isOpenMap_inl _ isOpen_Ioo⟩, ⟨a, ⟨hl, hu⟩, rfl⟩, ?_,
      fun _ _ => trivial, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact hsub hb
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ z hz
      obtain ⟨hpz, hzq⟩ := Causality.mem_diamond.1 hz
      rcases z with d | ⟨⟩
      · exact ⟨d, ⟨hb.1.trans_le hpz.1, hzq.1.trans_lt hc.2⟩, rfl⟩
      · exact hzq.elim
  · refine ⟨gateStar, ⟨(), rfl⟩, ?_, fun _ _ => trivial, ?_⟩
    · rintro _ ⟨u, rfl⟩
      exact mem_of_mem_nhds hN
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ z hz
      obtain ⟨hpz, -⟩ := Causality.mem_diamond.1 hz
      rcases z with d | ⟨⟩
      · exact hpz.elim
      · exact ⟨(), rfl⟩

/-- **The gated line is strongly causal** (`strongly_causal`, DEC-7). -/
theorem gateLine_stronglyCausal : gateLine.StronglyCausal :=
  gateLine_stronglyCausalOpen.stronglyCausal

/-! ## The separations -/

/-- **The printed causal openness is strictly weaker than DEC-8's two-sided one** (in the library's
reading of `defi:causalite`, without gluing; OQ-18)
(`causally_open_future ⇏ causally_open`; also `locally_causally_open`, `globally_hyperbolic`,
`is_causal`, `strongly_causal(_open)`, `curves_extend`, `locally_push_up ⇏ causally_open`). The
gated line is causally open in the future (`def:causally_open_spacetime_open` as printed), locally
causally open on both sides, globally hyperbolic, causal, strongly causal (both forms), with
curves extending and local push-up, and not causally open; it is not absolutely minimal, which
`prop:topological_spacetime_absolutely_minimal` (DEC-8 reading,
`AbsolutelyMinimal.causallyOpen_of_locallyCausallyOpen`) shows necessary. -/
theorem gateLine_separates_causallyOpen :
    gateLine.CausallyOpenFuture ∧ gateLine.LocallyCausallyOpen ∧ gateLine.GloballyHyperbolic ∧
      gateLine.IsCausal ∧ gateLine.StronglyCausalOpen ∧ gateLine.StronglyCausal ∧
      gateLine.CurvesExtend ∧ gateLine.LocallyPushUp ∧
      ¬ gateLine.toPrecausality.AbsolutelyMinimal ∧ ¬ gateLine.CausallyOpen :=
  ⟨gateLine_causallyOpenFuture, gateLine_locallyCausallyOpen,
    Causality.globallyHyperbolicOn_top.1 (gateLine_globallyHyperbolicOn (Or.inl rfl)),
    gateLine_isCausal, gateLine_stronglyCausalOpen, gateLine_stronglyCausal, gateLine_curvesExtend,
    gateLine_locallyPushUp,
    fun h => gateLine_not_absolutelyMinimalOn (Precausality.absolutelyMinimal_iff.1 h),
    gateLine_not_causallyOpen⟩

/-- **Local push-up does not give push-up without causal arc-connectedness**
(`locally_push_up ⇏ push_up`; also `globally_hyperbolic`, `is_causal`, `strongly_causal(_open)`,
`curves_extend`, `causally_open_future`, `locally_causally_open ⇏ push_up`): the cover of
`lem:pushup_local` exists on the gated line, which is globally hyperbolic, causal, strongly causal
(both forms), with curves extending, causally open in the future and locally causally open on both
sides, not causally arc-connected, and has not push-up. -/
theorem gateLine_separates_pushUp :
    gateLine.LocallyPushUp ∧ gateLine.GloballyHyperbolic ∧ gateLine.IsCausal ∧
      gateLine.StronglyCausalOpen ∧ gateLine.StronglyCausal ∧ gateLine.CurvesExtend ∧
      gateLine.CausallyOpenFuture ∧ gateLine.LocallyCausallyOpen ∧
      ¬ gateLine.CausallyArcConnected ∧ ¬ gateLine.PushUp :=
  ⟨gateLine_locallyPushUp,
    Causality.globallyHyperbolicOn_top.1 (gateLine_globallyHyperbolicOn (Or.inl rfl)),
    gateLine_isCausal, gateLine_stronglyCausalOpen, gateLine_stronglyCausal, gateLine_curvesExtend,
    gateLine_causallyOpenFuture,
    gateLine_locallyCausallyOpen, gateLine_cauchyInclusion_not_causallyConvex.2.2.2.2.1,
    gateLine_not_pushUp⟩

end Causal
