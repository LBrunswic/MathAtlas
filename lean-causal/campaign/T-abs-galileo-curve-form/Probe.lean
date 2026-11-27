import CausalScaffold.GalileoCurveForm

/-! Probe for T-abs-galileo-curve-form (2026-11-27): `#check` and `#print axioms` of every
declaration of `CausalScaffold.GalileoCurveForm`; the output is `axioms.txt`. Then one `example`
per `[[open]]` entry `X → locally_strongly_causal` that the witness settles (16 of the 18), each
`X` of `Causal.galileoCurve 1` with `¬ LocallyStronglyCausal`, read off
`Causal.galileoCurve_separates`, and one with the 16 positive ids together (the proposed
`[[fails]]` entry's `from`). Not built by lake. -/

open Causal

#check @galileoGraphLt
#check @galileoGraphLt.mem_left
#check @galileoGraphLt.mem_right
#check @galileoGraphLt.trans
#check @galileoGraphLt.mono
#check @isRelFamily_galileoGraphLt
#check @galileoGraphLt_of_segment_subset
#check @isOpen_galileoGraphLt_right
#check @isOpen_galileoGraphLt_left
#check @galileoCurveLt
#check @galileoCurveLt_of_continuousOn
#check @galileoCurveLt_iff_graphLt
#check @galileoCurve
#check @galileoCurve_lt
#check @galileoCurve_le
#check @galileoCurve_lt_iff_graphLt
#check @galileoCurve_lt_fst
#check @galileoCurve_le_fst
#check @galileoCurve_lt_of_segment_subset
#check @galileoCurve_lt_top
#check @galileoCurve_chronalCurveOn_iff
#check @galileoCurve_causallyArcConnected
#check @galileoCurve_lt_of_le_of_lt
#check @galileoCurve_lt_of_lt_of_le
#check @galileoCurve_pushUp
#check @galileoCurve_lt_vertical
#check @galileo_exists_vertical_subset
#check @galileoCurve_chronalNeighbours
#check @galileoCurve_isCausal
#check @galileoCurve_hasTimeFunction
#check @galileoCurve_isTimeFunction_fst
#check @galileoCurve_chronalHomotopyOn_convexCombination
#check @galileoCurve_futureOneConnectedOn
#check @galileoCurve_futureOneConnected
#check @galileoCurve_diamond_top
#check @galileoCurve_slab_subset_of_convex
#check @galileoCurve_not_causallyCompact
#check @galileoCurve_not_stronglyCausalOn
#check @galileoCurve_not_locallyStronglyCausal
#check @galileoCurve_lt_imp_galileo
#check @galileoCurve_le_imp_galileo
#check @galileoCurve_lt_iff_galileo_of_convex
#check @galileoCurve_le_iff_galileo_of_convex
#check @galileoCurve_lt_iff_transGen_convex
#check @galileoCurve_ne_galileo
#check @exists_galileo_lt_not_galileoCurve_lt
#check @galileoCurve_separates

#print axioms galileoGraphLt
#print axioms galileoGraphLt.mem_left
#print axioms galileoGraphLt.mem_right
#print axioms galileoGraphLt.trans
#print axioms galileoGraphLt.mono
#print axioms isRelFamily_galileoGraphLt
#print axioms galileoGraphLt_of_segment_subset
#print axioms isOpen_galileoGraphLt_right
#print axioms isOpen_galileoGraphLt_left
#print axioms galileoCurveLt
#print axioms galileoCurveLt_of_continuousOn
#print axioms galileoCurveLt_iff_graphLt
#print axioms galileoCurve
#print axioms galileoCurve_lt
#print axioms galileoCurve_le
#print axioms galileoCurve_lt_iff_graphLt
#print axioms galileoCurve_lt_fst
#print axioms galileoCurve_le_fst
#print axioms galileoCurve_lt_of_segment_subset
#print axioms galileoCurve_lt_top
#print axioms galileoCurve_chronalCurveOn_iff
#print axioms galileoCurve_causallyArcConnected
#print axioms galileoCurve_lt_of_le_of_lt
#print axioms galileoCurve_lt_of_lt_of_le
#print axioms galileoCurve_pushUp
#print axioms galileoCurve_lt_vertical
#print axioms galileo_exists_vertical_subset
#print axioms galileoCurve_chronalNeighbours
#print axioms galileoCurve_isCausal
#print axioms galileoCurve_hasTimeFunction
#print axioms galileoCurve_isTimeFunction_fst
#print axioms galileoCurve_chronalHomotopyOn_convexCombination
#print axioms galileoCurve_futureOneConnectedOn
#print axioms galileoCurve_futureOneConnected
#print axioms galileoCurve_diamond_top
#print axioms galileoCurve_slab_subset_of_convex
#print axioms galileoCurve_not_causallyCompact
#print axioms galileoCurve_not_stronglyCausalOn
#print axioms galileoCurve_not_locallyStronglyCausal
#print axioms galileoCurve_lt_imp_galileo
#print axioms galileoCurve_le_imp_galileo
#print axioms galileoCurve_lt_iff_galileo_of_convex
#print axioms galileoCurve_le_iff_galileo_of_convex
#print axioms galileoCurve_lt_iff_transGen_convex
#print axioms galileoCurve_ne_galileo
#print axioms exists_galileo_lt_not_galileoCurve_lt
#print axioms galileoCurve_separates

-- [[open]] causally_arc_connected → locally_strongly_causal
example : (galileoCurve 1).CausallyArcConnected ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨h1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h1, h19⟩

-- [[open]] absolutely_minimal → locally_strongly_causal
example : (galileoCurve 1).AbsolutelyMinimal ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, h2, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h2, h19⟩

-- [[open]] push_up → locally_strongly_causal
example : (galileoCurve 1).PushUp ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, h4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h4, h19⟩

-- [[open]] locally_push_up → locally_strongly_causal
example : (galileoCurve 1).LocallyPushUp ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, h5, _, _, _, _, _, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h5, h19⟩

-- [[open]] causally_open → locally_strongly_causal
example : (galileoCurve 1).CausallyOpen ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, h6, _, _, _, _, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h6, h19⟩

-- [[open]] causally_open_future → locally_strongly_causal
example : (galileoCurve 1).CausallyOpenFuture ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, h7, _, _, _, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h7, h19⟩

-- [[open]] locally_causally_open → locally_strongly_causal
example : (galileoCurve 1).LocallyCausallyOpen ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, h8, _, _, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h8, h19⟩

-- [[open]] locally_causally_open_future → locally_strongly_causal
example : (galileoCurve 1).LocallyCausallyOpenFuture ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, h9, _, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h9, h19⟩

-- [[open]] tarentin → locally_strongly_causal
example : (galileoCurve 1).Tarentin ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, _, h10, _, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h10, h19⟩

-- [[open]] chronal_neighbours → locally_strongly_causal
example : (galileoCurve 1).ChronalNeighbours ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, _, _, h11, _, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h11, h19⟩

-- [[open]] has_chronal_neighbour → locally_strongly_causal
example : (galileoCurve 1).HasChronalNeighbourEverywhere ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h12, h19⟩

-- [[open]] causally_plain → locally_strongly_causal
example : (galileoCurve 1).CausallyPlain ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, h13, _, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h13, h19⟩

-- [[open]] is_causal → locally_strongly_causal
example : (galileoCurve 1).IsCausal ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h14, _, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h14, h19⟩

-- [[open]] time_function → locally_strongly_causal
example : (galileoCurve 1).HasTimeFunction ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, _, _, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h15, h19⟩

-- [[open]] future_one_connected → locally_strongly_causal
example : (galileoCurve 1).FutureOneConnected ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h17, _, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h17, h19⟩

-- [[open]] curves_extend → locally_strongly_causal
example : (galileoCurve 1).CurvesExtend ∧ ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h18, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h18, h19⟩

-- the proposed [[fails]] entry: the 16 positive ids, and not locally_strongly_causal
example :
    (galileoCurve 1).CausallyArcConnected ∧
    (galileoCurve 1).AbsolutelyMinimal ∧
    (galileoCurve 1).PushUp ∧
    (galileoCurve 1).LocallyPushUp ∧
    (galileoCurve 1).CausallyOpen ∧
    (galileoCurve 1).CausallyOpenFuture ∧
    (galileoCurve 1).LocallyCausallyOpen ∧
    (galileoCurve 1).LocallyCausallyOpenFuture ∧
    (galileoCurve 1).Tarentin ∧
    (galileoCurve 1).ChronalNeighbours ∧
    (galileoCurve 1).HasChronalNeighbourEverywhere ∧
    (galileoCurve 1).CausallyPlain ∧
    (galileoCurve 1).IsCausal ∧
    (galileoCurve 1).HasTimeFunction ∧
    (galileoCurve 1).FutureOneConnected ∧
    (galileoCurve 1).CurvesExtend ∧
    ¬ (galileoCurve 1).LocallyStronglyCausal :=
  let ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _, h17, h18, h19, _, _, _, _⟩ := galileoCurve_separates le_rfl
  ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19⟩

-- the agreement on convex opens, and the difference for n ≥ 1
example (U : TopologicalSpace.Opens (ℝ × (Fin 1 → ℝ))) (hU : Convex ℝ (U : Set (ℝ × (Fin 1 → ℝ))))
    (p q : ℝ × (Fin 1 → ℝ)) : (galileoCurve 1).le U p q ↔ (galileo 1).le U p q :=
  galileoCurve_le_iff_galileo_of_convex hU
example : galileoCurve 1 ≠ galileo 1 := galileoCurve_ne_galileo le_rfl
