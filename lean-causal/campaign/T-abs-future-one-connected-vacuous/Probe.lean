import CausalScaffold.FutureOneConnectedVacuous

/-! Probe for T-abs-future-one-connected-vacuous: the declarations, their axioms, and the 18
pairs `future_one_connected ⇏ X` of the ladder, each projected from its witness. -/

namespace Causal

open TopologicalSpace

#check @Causal.Causality.not_chronalCurveOn_of_forall_not_lt
#check @Causal.Causality.futureOneConnectedOn_of_forall_not_lt
#check @Causal.Causality.withoutChronology_futureOneConnectedOn
#check @Causal.Causality.withoutChronology_futureOneConnected
#check @Causal.Causality.pushUp_of_forall_not_lt
#check @Causal.Causality.not_hasChronalNeighbourEverywhere_of_forall_not_lt
#check @Causal.Causality.not_causallyPlain_of_forall_not_lt
#check @Causal.halfChronoLine_chronalCurveOn_iff
#check @Causal.halfChronoLine_chronalCurveOn_iff_strictMonoOn
#check @Causal.halfChronoLine_futureOneConnectedOn
#check @Causal.halfChronoLine_not_hasChronalNeighbourEverywhere
#check @Causal.rationalLine_separates_futureOneConnected
#check @Causal.lightlikeLine_separates_futureOneConnected
#check @Causal.halfChronoLine_separates_futureOneConnected
#check @Causal.jumpLine_separates_futureOneConnected
#check @Causal.symmRationalLine_separates_futureOneConnected

#print axioms Causal.Causality.not_chronalCurveOn_of_forall_not_lt
#print axioms Causal.Causality.futureOneConnectedOn_of_forall_not_lt
#print axioms Causal.Causality.withoutChronology_futureOneConnectedOn
#print axioms Causal.Causality.withoutChronology_futureOneConnected
#print axioms Causal.Causality.pushUp_of_forall_not_lt
#print axioms Causal.Causality.not_hasChronalNeighbourEverywhere_of_forall_not_lt
#print axioms Causal.Causality.not_causallyPlain_of_forall_not_lt
#print axioms Causal.halfChronoLine_chronalCurveOn_iff
#print axioms Causal.halfChronoLine_chronalCurveOn_iff_strictMonoOn
#print axioms Causal.halfChronoLine_futureOneConnectedOn
#print axioms Causal.halfChronoLine_not_hasChronalNeighbourEverywhere
#print axioms Causal.rationalLine_separates_futureOneConnected
#print axioms Causal.lightlikeLine_separates_futureOneConnected
#print axioms Causal.halfChronoLine_separates_futureOneConnected
#print axioms Causal.jumpLine_separates_futureOneConnected
#print axioms Causal.symmRationalLine_separates_futureOneConnected

/-! The 18 pairs, each as a closed statement on `ℝ`: no causality on `ℝ` that is future
one-connected need be `X`, and the witness's own reading of minimality beside it. -/

-- future_one_connected → absolutely_minimal: jumpLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.AbsolutelyMinimal := by
  intro h
  have w := jumpLine_separates_futureOneConnected
  have hn : ¬ jumpLine.AbsolutelyMinimal := by tauto
  exact hn (h _ w.1)

-- future_one_connected → causally_arc_connected: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.CausallyArcConnected := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.CausallyArcConnected := by tauto
  exact hn (h _ w.1)

-- future_one_connected → causally_compact: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.CausallyCompact := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.CausallyCompact := by tauto
  exact hn (h _ w.1)

-- future_one_connected → causally_open: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.CausallyOpen := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.CausallyOpen := by tauto
  exact hn (h _ w.1)

-- future_one_connected → causally_open_future: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.CausallyOpenFuture := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.CausallyOpenFuture := by tauto
  exact hn (h _ w.1)

-- future_one_connected → causally_plain: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.CausallyPlain := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.CausallyPlain := by tauto
  exact hn (h _ w.1)

-- future_one_connected → chronal_neighbours: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.ChronalNeighbours := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.ChronalNeighbours := by tauto
  exact hn (h _ w.1)

-- future_one_connected → globally_hyperbolic: symmRationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.GloballyHyperbolic := by
  intro h
  have w := symmRationalLine_separates_futureOneConnected
  have hn : ¬ symmRationalLine.GloballyHyperbolic := by tauto
  exact hn (h _ w.1)

-- future_one_connected → has_chronal_neighbour: lightlikeLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.HasChronalNeighbourEverywhere := by
  intro h
  have w := lightlikeLine_separates_futureOneConnected
  have hn : ¬ lightlikeLine.HasChronalNeighbourEverywhere := by tauto
  exact hn (h _ w.1)

-- future_one_connected → is_causal: symmRationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.IsCausal := by
  intro h
  have w := symmRationalLine_separates_futureOneConnected
  have hn : ¬ symmRationalLine.IsCausal := by tauto
  exact hn (h _ w.1)

-- future_one_connected → locally_causally_open: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.LocallyCausallyOpen := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.LocallyCausallyOpen := by tauto
  exact hn (h _ w.1)

-- future_one_connected → locally_causally_open_future: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.LocallyCausallyOpenFuture := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.LocallyCausallyOpenFuture := by tauto
  exact hn (h _ w.1)

-- future_one_connected → locally_push_up: halfChronoLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.LocallyPushUp := by
  intro h
  have w := halfChronoLine_separates_futureOneConnected
  have hn : ¬ halfChronoLine.LocallyPushUp := by tauto
  exact hn (h _ w.1)

-- future_one_connected → push_up: halfChronoLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.PushUp := by
  intro h
  have w := halfChronoLine_separates_futureOneConnected
  have hn : ¬ halfChronoLine.PushUp := by tauto
  exact hn (h _ w.1)

-- future_one_connected → strongly_causal: symmRationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.StronglyCausal := by
  intro h
  have w := symmRationalLine_separates_futureOneConnected
  have hn : ¬ symmRationalLine.StronglyCausal := by tauto
  exact hn (h _ w.1)

-- future_one_connected → strongly_causal_open: symmRationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.StronglyCausalOpen := by
  intro h
  have w := symmRationalLine_separates_futureOneConnected
  have hn : ¬ symmRationalLine.StronglyCausalOpen := by tauto
  exact hn (h _ w.1)

-- future_one_connected → tarentin: rationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.Tarentin := by
  intro h
  have w := rationalLine_separates_futureOneConnected
  have hn : ¬ rationalLine.Tarentin := by tauto
  exact hn (h _ w.1)

-- future_one_connected → time_function: symmRationalLine
example : ¬ ∀ C : Causality ℝ, C.FutureOneConnected → C.HasTimeFunction := by
  intro h
  have w := symmRationalLine_separates_futureOneConnected
  have hn : ¬ symmRationalLine.HasTimeFunction := by tauto
  exact hn (h _ w.1)

example : rationalLine.FutureOneConnected ∧ ∀ W : Opens ℝ, rationalLine.AbsolutelyMinimalOn W := by
  have w := rationalLine_separates_futureOneConnected
  tauto

example : lightlikeLine.FutureOneConnected ∧ ∀ W : Opens ℝ, lightlikeLine.AbsolutelyMinimalOn W := by
  have w := lightlikeLine_separates_futureOneConnected
  tauto

example : halfChronoLine.FutureOneConnected ∧ ∀ W : Opens ℝ, halfChronoLine.AbsolutelyMinimalOn W := by
  have w := halfChronoLine_separates_futureOneConnected
  tauto

example : symmRationalLine.FutureOneConnected ∧ ∀ W : Opens ℝ, symmRationalLine.AbsolutelyMinimalOn W := by
  have w := symmRationalLine_separates_futureOneConnected
  tauto

-- the jump line is not absolutely minimal, so it carries no hereditary minimality
example : jumpLine.FutureOneConnected ∧ ¬ jumpLine.AbsolutelyMinimal := by
  have w := jumpLine_separates_futureOneConnected
  tauto

end Causal
