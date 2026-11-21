import Causal.NestedConverse
import Causal.LadderLocal
import Causal.CurvesExtend
import Causal.Ladder.Rules

/-!
# The rational line in the ladder: a time function and open strong causality; not locally causally open in the future, not tarentin, not causally plain, no chronal neighbours, not causally compact

Programme target `T-abs-rational-line-extras` (`programme/roadmap.toml:800`; layer 1, no label of
`ETT.tex`). Imports: `Causal.NestedConverse` (the rational line), `Causal.LadderLocal`,
`Causal.CurvesExtend`, `Causal.Ladder.Rules` (the `causal_ladder` tactic), all ETT layer: no model,
no CBG, Splitting, LemmaK* or LevinUtility module, transitively. Each property is stated with the
ladder's definition (`programme/ladder.toml`, the `lean` field of its `[[property]]`).

* **`T-abs-rational-line-extras/1-time-function`** — `rationalLine_hasTimeFunction` (the identity:
  `x ≤_M y` with `x ≠ y` is `x < y`); `rationalLine_curvesExtend`.
* **`T-abs-rational-line-extras/2-strongly-causal-open`** — `rationalLine_stronglyCausalOpen` (an
  open interval is causally convex: `J_M(p, q) ⊆ [p, q]`, `rationalLine_diamond_subset_Icc`);
  `rationalLine_stronglyCausal`.
* **`T-abs-rational-line-extras/3-not-locally-causally-open-future`** —
  `rationalLine_not_locallyCausallyOpenFuture`, by `causal_ladder` through the edge
  `absolutely_minimal ∧ locally_causally_open_future ⇒ causally_open_future`
  (`Causality.AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture`) and
  `rationalLine_not_causallyOpenFuture`; `rationalLine_not_locallyCausallyOpen`.
* **`T-abs-rational-line-extras/4-not-tarentin`** — `rationalLine_not_tarentin`: an irrational
  point of a diamond `J_M(p, q)` is `p` (`rationalLine_eq_of_le_irrational`), so no diamond has
  interior (`rationalLine_openDiamond`).
* **`T-abs-rational-line-extras/5-not-causally-plain`** — `rationalLine_not_causallyPlain`:
  `Int J⁺_M(ℝ) = ℝ` while `I⁺_M(ℝ) = ∅`.
* **`T-abs-rational-line-extras/6-no-chronal-neighbours`** — `rationalLine_not_chronalNeighbours`
  (`≪` is empty).
* **`T-abs-rational-line-extras/7-not-causally-compact`** — `rationalLine_diamond_top`
  (`J_M(p, q) = ℚ ∩ [p, q]` for rationals `p`, `q`), `rationalLine_not_causallyCompact`
  (`ℚ ∩ [0, 1]` is not closed); `rationalLine_not_globallyHyperbolic`.
* **`T-abs-rational-line-extras/8-separation`** — `rationalLine_separates`, the conjoined witness:
  the facts of `rationalLine_separates_absolutelyMinimal` with the ones above; and, for the reading,
  `rationalLine_absolutelyMinimalOn` (absolutely minimal on every open set for every cover of it).

> the identity is continuous and strictly increasing along ≤; an interval V ⊆ U is causally
> convex (J_⊤(p, q) ⊆ [p, q]); ¬ LocallyCausallyOpenFuture from
> AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture (Causal/LadderLocal.lean:264)
> […]; ¬ Tarentin (each J_⊤(p, q) ⊆ ℚ has empty interior); ¬ CausallyPlain and ¬ ChronalNeighbours
> (≪ empty, J⁺ of a non-empty open set has interior); ¬ CausallyCompact (ℚ ∩ [p, q] is not
> closed). (`programme/roadmap.toml:810`, evidence)

> A topological spacetime $M$ is tarentin if for every $x\in M$ and every neighbourhood $\U$ of
> $x$ there exist $p,q\in \U$ such that $x\in \mathrm{Int}\left(J_M(p,q)\right)$.
> (`def:tarentin_spacetime`, `ETT.tex:677–680`)

> Let $(M,\leq,\ll)$ be a topological spacetime. $M$ is causally compact if the diamond $J(p,q)$
> is compact for all $p,q\in M$. (`def:causally_compact`, `ETT.tex:350–352`)

## Hypothesis checklist

| target claim | here |
|---|---|
| a time function, the identity (`HasTimeFunction`) | ✓ proved |
| open strong causality, intervals causally convex (`StronglyCausalOpen`) | ✓ proved; `J_M(p, q) ⊆ [p, q]` holds in every open, not only at `M` |
| ¬ `LocallyCausallyOpenFuture`, via absolute minimality and ¬ `CausallyOpenFuture` | ✓ proved, by `causal_ladder` |
| ¬ `Tarentin`, diamonds inside `ℚ` have empty interior | ✓ proved; a diamond lies in `ℚ ∪ {p}`, which is what the proof uses (`J_M(p, p) = {p}` with `p` irrational) |
| ¬ `CausallyPlain`, ¬ `ChronalNeighbours` (`≪` empty) | ✓ proved |
| ¬ `CausallyCompact`, `J(p, q) = ℚ ∩ [p, q]` not closed | ✓ proved, for rationals `p`, `q`; the witness is `J(0, 1)` |

## SCOPE (disclosed)

* Every argued fact of the target's evidence is confirmed against the compiled definitions; none
  is refuted. One precision: `J_M(p, q) = ℚ ∩ [p, q]` holds for rationals `p`, `q`; when `p` or
  `q` is irrational the diamond is `{p}` (if `p = q`) or empty.
* The rational line is absolutely minimal (`rationalLine_absolutelyMinimal`), and on every open set
  for every cover of it (`rationalLine_absolutelyMinimalOn`), so every separation it gives holds in
  either reading of `defi:causalite` (OQ-18): the gluing reading asks exactly this. The proof of
  the latter takes a Lebesgue number of the cover (a metric lemma inside the proof only).
* `ℝ` is Hausdorff and second countable (mathlib instances): the line is one of ETT's spacetimes.
  No metric notion appears in a statement; the proofs use the order of `ℝ`, its topology, the
  density of `ℚ` and of the irrationals, and one Lebesgue number (above).
* Names checked unique against `Causal/` and the scaffold.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

/-! ## The relation, read on `ℝ` -/

/-- `x ≤_U y` on the rational line gives `x ≤ y` in `ℝ`. -/
theorem rationalLine_le_real {U : Opens ℝ} {x y : ℝ} (h : rationalLine.le U x y) : x ≤ y := by
  rcases rationalLine_le.1 h with ⟨rfl, -⟩ | ⟨h, -⟩
  · exact le_rfl
  · exact h.le

/-- `x ≤_U y` on the rational line with `y` irrational is `x = y`. -/
theorem rationalLine_eq_of_le_irrational {U : Opens ℝ} {x y : ℝ} (h : rationalLine.le U x y)
    (hy : Irrational y) : x = y := by
  rcases rationalLine_le.1 h with ⟨h, -⟩ | ⟨-, -, hq, -⟩
  · exact h
  · exact (hy hq).elim

/-- Every diamond of the rational line lies in the segment: `J_U(p, q) ⊆ [p, q]`. -/
theorem rationalLine_diamond_subset_Icc (U : Opens ℝ) (p q : ℝ) :
    rationalLine.diamond U p q ⊆ Icc p q := by
  intro x hx
  rw [Causality.mem_diamond] at hx
  exact ⟨rationalLine_le_real hx.1, rationalLine_le_real hx.2⟩

/-- **The full diamond between rationals**: `J_M(p, q) = ℚ ∩ [p, q]` for rationals `p`, `q` (both
sides are empty when `q < p`). -/
theorem rationalLine_diamond_top (p q : ℚ) :
    rationalLine.diamond ⊤ (p : ℝ) q = range ((↑) : ℚ → ℝ) ∩ Icc (p : ℝ) q := by
  ext x
  simp only [Causality.mem_diamond, mem_inter_iff, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, rationalLine_le_real h1, rationalLine_le_real h2⟩
    rcases rationalLine_le.1 h1 with ⟨rfl, -⟩ | ⟨-, -, hx, -⟩
    · exact ⟨p, rfl⟩
    · exact hx
  · rintro ⟨hx, hpx, hxq⟩
    refine ⟨?_, ?_⟩
    · rcases hpx.eq_or_lt with h | h
      · exact Or.inl ⟨h, trivial⟩
      · exact Or.inr ⟨h, ⟨p, rfl⟩, hx, fun _ _ => trivial⟩
    · rcases hxq.eq_or_lt with h | h
      · exact Or.inl ⟨h, trivial⟩
      · exact Or.inr ⟨h, hx, ⟨q, rfl⟩, fun _ _ => trivial⟩

/-- **No diamond of the rational line has interior**: an irrational point of `J_U(p, q)` is `p`,
and every open interval holds two irrationals. -/
theorem rationalLine_openDiamond (U : Opens ℝ) (p q : ℝ) :
    rationalLine.openDiamond U p q = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨v, hv, hlv, hvx⟩ := exists_irrational_btwn hl
  obtain ⟨w, hw, hxw, hwu⟩ := exists_irrational_btwn hu
  have h1 := (Causality.mem_diamond.1 (hlu ⟨hlv, hvx.trans hu⟩)).1
  have h2 := (Causality.mem_diamond.1 (hlu ⟨hl.trans hxw, hwu⟩)).1
  have hvw : v = w :=
    (rationalLine_eq_of_le_irrational h1 hv).symm.trans (rationalLine_eq_of_le_irrational h2 hw)
  linarith

/-! ## The positive facts -/

/-- **The rational line is absolutely minimal on every open set, for every cover of it**: on every
open `W` the relations are generated by the restrictions to any open cover of `W` — the gluing
reading of `defi:causalite` (OQ-18), not only the library's. The proof of
`rationalLine_absolutelyMinimal` (the case `W = ⊤`), with the cover asked of `W` only: equal
rational steps below a Lebesgue number of the cover of the segment `[q, q'] ⊆ V ⊆ W`. -/
theorem rationalLine_absolutelyMinimalOn (W : Opens ℝ) : rationalLine.AbsolutelyMinimalOn W := by
  intro S hS V hVW x y
  refine ⟨fun hxy => ?_, fun hxy => False.elim hxy⟩
  rcases rationalLine_le.1 hxy with ⟨rfl, hx⟩ | ⟨hlt, ⟨q, rfl⟩, ⟨q', rfl⟩, hsub⟩
  · obtain ⟨O, hO, hxO⟩ := hS x (hVW hx)
    exact Relation.TransGen.single ⟨O, hO, rationalLine.le_refl ⟨hx, hxO⟩⟩
  -- a Lebesgue number `δ` of the cover `V ⊓ O` of `[q, q']`, and `n` equal rational steps `< δ`
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := (q : ℝ)) (b := q'))
    (c := fun O : S => ((V ⊓ (O : Opens ℝ) : Opens ℝ) : Set ℝ)) (fun _ => Opens.isOpen _)
    (fun z hz => by
      obtain ⟨O, hO, hzO⟩ := hS z (hVW (hsub hz))
      exact mem_iUnion.2 ⟨⟨O, hO⟩, hsub hz, hzO⟩)
  have hd0 : (0 : ℝ) < (q' : ℝ) - q := sub_pos.2 hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (((q' : ℝ) - q) / δ)
  have hn0 : (0 : ℝ) < n := (div_pos hd0 hδ).trans hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast hn0.ne')
  set d : ℝ := ((q' : ℝ) - q) / ((m + 1 : ℕ) : ℝ) with hd
  have hdpos : 0 < d := div_pos hd0 hn0
  have hdδ : d < δ := by
    rw [hd, div_lt_iff₀ hn0]; rw [div_lt_iff₀ hδ] at hn; linarith
  have hnd : ((m + 1 : ℕ) : ℝ) * d = (q' : ℝ) - q := by rw [hd]; field_simp
  let p : ℕ → ℝ := fun k => (q : ℝ) + k * d
  have hprat : ∀ k : ℕ, p k ∈ range ((↑) : ℚ → ℝ) := fun k =>
    ⟨q + k * ((q' - q) / ((m + 1 : ℕ) : ℚ)), by simp only [p, hd]; push_cast; ring⟩
  have hstep : ∀ k : ℕ, k < m + 1 → ∃ O ∈ S, rationalLine.le (V ⊓ O) (p k) (p (k + 1)) := by
    intro k hk
    have hkn : (k : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    have hpk : p k ∈ Icc (q : ℝ) q' := ⟨by simp only [p]; nlinarith, by simp only [p]; nlinarith⟩
    obtain ⟨⟨O, hO⟩, hOb⟩ := hball (p k) hpk
    refine ⟨O, hO, Or.inr ⟨by simp only [p]; push_cast; linarith, hprat k, hprat (k + 1),
      fun z hz => hOb ?_⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    simp only [p] at hz; push_cast at hz
    constructor <;> linarith [hz.1, hz.2]
  have hchain : ∀ k : ℕ, k < m + 1 →
      Relation.TransGen (fun a b => ∃ O ∈ S, rationalLine.le (V ⊓ O) a b) (p 0) (p (k + 1)) := by
    intro k
    induction k with
    | zero => intro h0; exact Relation.TransGen.single (hstep 0 h0)
    | succ k ih => intro hk; exact (ih (Nat.lt_of_succ_lt hk)).tail (hstep (k + 1) hk)
  have h0 : p 0 = q := by simp [p]
  have hN : p (m + 1) = q' := by simp only [p]; rw [hnd]; ring
  rw [← h0, ← hN]
  exact hchain m (Nat.lt_succ_self m)

/-- **The rational line has a time function** (the ladder node `time_function`): the identity. -/
theorem rationalLine_hasTimeFunction : rationalLine.HasTimeFunction :=
  ⟨id, continuous_id, fun _ _ hxy hne => (rationalLine_le_real hxy).lt_of_ne hne⟩

/-- Causal curves of the rational line extend (through its time function). -/
theorem rationalLine_curvesExtend : rationalLine.CurvesExtend :=
  rationalLine_hasTimeFunction.curvesExtend

/-- **The rational line is strongly causal in the open form** (the ladder node
`strongly_causal_open`): an open interval is causally convex in `M`. -/
theorem rationalLine_stronglyCausalOpen : rationalLine.StronglyCausalOpen := by
  intro p N hN
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
  refine ⟨⟨Ioo l u, isOpen_Ioo⟩, ⟨hl, hu⟩, hlu, fun _ _ => trivial, fun a ha b hb x hx => ?_⟩
  have hx' := rationalLine_diamond_subset_Icc ⊤ a b hx
  exact ⟨ha.1.trans_le hx'.1, hx'.2.trans_lt hb.2⟩

/-- The rational line is strongly causal. -/
theorem rationalLine_stronglyCausal : rationalLine.StronglyCausal :=
  rationalLine_stronglyCausalOpen.stronglyCausal

/-- The rational line has local push-up. -/
theorem rationalLine_locallyPushUp : rationalLine.LocallyPushUp :=
  rationalLine_pushUp.locallyPushUp

/-! ## The negative facts -/

/-- **The rational line is not locally causally open in the future**: it is absolutely minimal,
so local causal openness in the future would make it causally open in the future
(`prop:topological_spacetime_absolutely_minimal` as printed), which it is not. -/
theorem rationalLine_not_locallyCausallyOpenFuture :
    ¬ rationalLine.LocallyCausallyOpenFuture := by
  intro h
  have hm := rationalLine_absolutelyMinimal
  exact rationalLine_not_causallyOpenFuture (by causal_ladder)

/-- The rational line is not locally causally open (two-sided). -/
theorem rationalLine_not_locallyCausallyOpen : ¬ rationalLine.LocallyCausallyOpen := by
  intro h
  exact rationalLine_not_locallyCausallyOpenFuture (by causal_ladder)

/-- **The rational line is not tarentin**: its open diamonds are empty. -/
theorem rationalLine_not_tarentin : ¬ rationalLine.Tarentin := by
  intro h
  obtain ⟨p, -, q, -, hx⟩ := h 0 univ Filter.univ_mem
  simp [rationalLine_openDiamond] at hx

/-- **The rational line is not causally plain**: `Int J⁺_M(ℝ) = ℝ` while `I⁺_M(ℝ) = ∅`. -/
theorem rationalLine_not_causallyPlain : ¬ rationalLine.CausallyPlain := by
  intro h
  have hJ : rationalLine.Jplus ⊤ univ = univ :=
    eq_univ_of_forall fun y => ⟨y, trivial, rationalLine.le_refl trivial⟩
  have hI : rationalLine.Iplus ⊤ univ = ∅ := eq_empty_of_forall_notMem fun _ ⟨_, _, h⟩ => h
  have h0 := (h ⊤ univ).1 (show (0 : ℝ) ∈ interior (rationalLine.Jplus ⊤ univ) by
    rw [hJ, interior_univ]; trivial)
  rw [hI, closure_empty] at h0
  exact h0

/-- The rational line has no chronal neighbours: `≪` is empty. -/
theorem rationalLine_not_chronalNeighbours : ¬ rationalLine.ChronalNeighbours := by
  intro h
  obtain ⟨_, _, hp⟩ := h.1 ⊤ 0 trivial
  exact hp

/-- **The rational line is not causally compact**: `J_M(0, 1) = ℚ ∩ [0, 1]` is not closed. -/
theorem rationalLine_not_causallyCompact : ¬ rationalLine.CausallyCompact := by
  intro h
  have hc := (h ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ)).isClosed
  rw [rationalLine_diamond_top] at hc
  obtain ⟨v, hv, hv0, hv1⟩ := exists_irrational_btwn (show ((0 : ℚ) : ℝ) < ((1 : ℚ) : ℝ) by simp)
  have hcl : v ∈ closure (range ((↑) : ℚ → ℝ) ∩ Icc ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ)) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 ht
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt hl hv0)
    exact ⟨r, hlu ⟨(le_max_left _ _).trans_lt hr1, hr2.trans hu⟩, ⟨r, rfl⟩,
      ((le_max_right _ _).trans_lt hr1).le, (hr2.trans hv1).le⟩
  rw [hc.closure_eq] at hcl
  exact hv hcl.1

/-- The rational line is not globally hyperbolic. -/
theorem rationalLine_not_globallyHyperbolic : ¬ rationalLine.GloballyHyperbolic := by
  intro h
  exact rationalLine_not_causallyCompact h.causallyCompact

/-! ## The separation -/

/-- **The rational line in the ladder, in one statement** (the keeper's conjoined witness). It is
absolutely minimal, causal, with push-up (hence locally), a time function (hence curves extend),
strongly causal in both forms; it is neither causally arc-connected, nor causally open in the
future (nor two-sided), nor locally causally open in the future (nor two-sided), nor tarentin, nor
causally plain, nor causally compact (nor globally hyperbolic), and has no chronal neighbours.
Absolutely minimal on every open set for every cover (`rationalLine_absolutelyMinimalOn`): every
separation holds in either reading of `defi:causalite` (OQ-18). -/
theorem rationalLine_separates :
    rationalLine.AbsolutelyMinimal ∧ rationalLine.IsCausal ∧ rationalLine.PushUp ∧
      rationalLine.LocallyPushUp ∧ rationalLine.HasTimeFunction ∧ rationalLine.CurvesExtend ∧
      rationalLine.StronglyCausalOpen ∧ rationalLine.StronglyCausal ∧
      ¬ rationalLine.CausallyArcConnected ∧ ¬ rationalLine.CausallyOpenFuture ∧
      ¬ rationalLine.CausallyOpen ∧ ¬ rationalLine.LocallyCausallyOpenFuture ∧
      ¬ rationalLine.LocallyCausallyOpen ∧ ¬ rationalLine.Tarentin ∧
      ¬ rationalLine.CausallyPlain ∧ ¬ rationalLine.ChronalNeighbours ∧
      ¬ rationalLine.CausallyCompact ∧ ¬ rationalLine.GloballyHyperbolic :=
  ⟨rationalLine_absolutelyMinimal, rationalLine_isCausal, rationalLine_pushUp,
    rationalLine_locallyPushUp, rationalLine_hasTimeFunction, rationalLine_curvesExtend,
    rationalLine_stronglyCausalOpen, rationalLine_stronglyCausal,
    rationalLine_not_causallyArcConnected, rationalLine_not_causallyOpenFuture,
    rationalLine_not_causallyOpen, rationalLine_not_locallyCausallyOpenFuture,
    rationalLine_not_locallyCausallyOpen, rationalLine_not_tarentin,
    rationalLine_not_causallyPlain, rationalLine_not_chronalNeighbours,
    rationalLine_not_causallyCompact, rationalLine_not_globallyHyperbolic⟩

end Causal
