import CausalScaffold.LscSeparations

/-! Probe for T-abs-lsc-separations (2026-11-27): `#check` and `#print axioms` of every theorem and the box of
`CausalScaffold.LscSeparations`; the output is `axioms.txt`. Then `example`s that read, off the two
witnesses, each settled `[[open]]` pair's `from` with its negated `to`; the ladder step
`strongly_causal ⇒ locally_strongly_causal` read backwards by `causal_ladder`; and the ladder's
ball of radius `1/2` about `a` (heredity from `loopLow`). Not built by lake. -/

open Causal TopologicalSpace

#check @ArcCoherent.mem_diamond_on
#check @ArcCoherent.causallyConvexIn_on
#check @symmRationalLine_not_stronglyCausalOn
#check @symmRationalLine_not_locallyStronglyCausal
#check @symmRationalLine_separates_locallyStronglyCausal
#check @loopFan_causallyConvexIn_box
#check @loopFan_stronglyCausalOn_of_boxes
#check @loopFan_stronglyCausalOn_low
#check @loopFan_stronglyCausalOn_side
#check @loopFan_stronglyCausalOn_cap
#check @loopPeak_mem_cap_iff
#check @loopFan_locallyStronglyCausal
#check @loopFan_stronglyCausalOn_low_not_at
#check @loopFan_separates_locallyStronglyCausal
#check @isOpen_loopBox
#check @loopγ_val_of_mem
#check @loopHeight_le
#check @loopHeight_le_top
#check @loopA_mem_loopLow
#check @loopSet_cases
#check @eq_half_of_loopγ_fst
#check @combEps_two_mul_sub_le

#print axioms ArcCoherent.mem_diamond_on
#print axioms ArcCoherent.causallyConvexIn_on
#print axioms symmRationalLine_not_stronglyCausalOn
#print axioms symmRationalLine_not_locallyStronglyCausal
#print axioms symmRationalLine_separates_locallyStronglyCausal
#print axioms loopFan_causallyConvexIn_box
#print axioms loopFan_stronglyCausalOn_of_boxes
#print axioms loopFan_stronglyCausalOn_low
#print axioms loopFan_stronglyCausalOn_side
#print axioms loopFan_stronglyCausalOn_cap
#print axioms loopPeak_mem_cap_iff
#print axioms loopFan_locallyStronglyCausal
#print axioms loopFan_stronglyCausalOn_low_not_at
#print axioms loopFan_separates_locallyStronglyCausal
#print axioms isOpen_loopBox
#print axioms loopγ_val_of_mem
#print axioms loopHeight_le
#print axioms loopHeight_le_top
#print axioms loopA_mem_loopLow
#print axioms loopSet_cases
#print axioms eq_half_of_loopγ_fst
#print axioms combEps_two_mul_sub_le

-- the five pairs X → locally_strongly_causal (X = future_one_connected, absolutely_minimal, push_up,
-- locally_push_up, curves_extend), read off the one witness, either reading
example : symmRationalLine.FutureOneConnected ∧ symmRationalLine.AbsolutelyMinimal ∧
    (∀ W : Opens ℝ, symmRationalLine.AbsolutelyMinimalOn W) ∧ symmRationalLine.PushUp ∧
    symmRationalLine.LocallyPushUp ∧ symmRationalLine.CurvesExtend ∧
    ¬ symmRationalLine.LocallyStronglyCausal :=
  let ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h₂₃, _⟩ :=
    symmRationalLine_separates_locallyStronglyCausal
  ⟨h₁, h₃, h₄, h₅, h₆, h₇, h₂₃⟩

-- the two pairs locally_strongly_causal → strongly_causal, strongly_causal_open, with the rest of
-- the existing entry's `from`, either reading
example : loopFan.LocallyStronglyCausal ∧ loopFan.AbsolutelyMinimal ∧
    (∀ W : Opens loopSet, loopFan.AbsolutelyMinimalOn W) ∧ loopFan.CausallyArcConnected ∧
    loopFan.GloballyHyperbolic ∧ loopFan.HasTimeFunction ∧
    ¬ loopFan.StronglyCausal ∧ ¬ loopFan.StronglyCausalOpen :=
  let ⟨_, _, h₃, h₄, h₅, _, _, _, _, h₁₀, h₁₁, _, _, _, h₁₅, h₁₆, h₁₇, _, _, _, _⟩ :=
    loopFan_separates_locallyStronglyCausal
  ⟨h₁₅, h₃, h₄, h₅, h₁₀, h₁₁, h₁₆, h₁₇⟩

-- the edge strongly_causal ⇒ locally_strongly_causal, read backwards by causal_ladder (kb/0080)
example : ¬ symmRationalLine.StronglyCausal := fun _ =>
  symmRationalLine_not_locallyStronglyCausal (by causal_ladder)

-- the ladder's ball of radius 1/2 about a: strongly causal as a spacetime, by heredity
example : loopFan.StronglyCausalOn ⟨Metric.ball loopA (1 / 2), Metric.isOpen_ball⟩ :=
  loopFan_stronglyCausalOn_low.mono fun z hz => by
    have h : dist z loopA < 1 / 2 := hz
    rw [Subtype.dist_eq, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, loopA_val] at h
    show z.val.2 < 1
    have := (abs_lt.1 h.2).2
    simp only [sub_zero] at this
    linarith

-- the old witnesses are projections of the new ones
example : loopFan.CausallyArcConnected ∧ ¬ loopFan.StronglyCausal :=
  let ⟨_, _, _, _, h₅, _, _, _, _, _, _, _, _, _, _, h₁₆, _, _, _, _, _⟩ :=
    loopFan_separates_locallyStronglyCausal
  ⟨h₅, h₁₆⟩
