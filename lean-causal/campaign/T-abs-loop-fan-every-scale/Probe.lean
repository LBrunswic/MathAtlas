import CausalScaffold.LoopFanEveryScale

/-! Probe for T-abs-loop-fan-every-scale (2026-11-27): `#check` and `#print axioms` of every
declaration of `CausalScaffold.LoopFanEveryScale`; the output is `axioms.txt`. Then `example`s that
read, off the one witness, the two pairs it settles (`globally_hyperbolic`,
`causally_compact ⇏ locally_strongly_causal`) with the whole `from` of the proposed entry; the
ladder steps read backwards by `causal_ladder`; level `0` as a linear copy of the loop fan; and the
contrast with the loop fan alone, which is locally strongly causal. Not built by lake. -/

open Causal TopologicalSpace

#check @fanScale
#check @fanScale_pos
#check @fanScale_two_mul_le
#check @fanScale_zero
#check @fanScale_one
#check @combEps_zero
#check @combEps_one
#check @levelEmbed
#check @continuous_levelEmbed
#check @levelEmbed_injective
#check @scaledFanArc
#check @scaledFanSet
#check @scaledFanγ
#check @scaledFanA
#check @scaledFan
#check @continuous_scaledFanγ
#check @scaledFanγ_val
#check @scaledFanγ_plane
#check @loopArc_snd_of_fst_eq_zero
#check @scaledFanArc_level_eq
#check @scaledFanγ_coherent
#check @scaledFan_le_iff
#check @scaledFanP_val
#check @scaledFanQ_val
#check @scaledFanPeak_val
#check @scaledFanA_val
#check @tendsto_scaledFanP
#check @tendsto_scaledFanQ
#check @abs_loopArc_fst_le
#check @loopArc_snd_mem
#check @scaledFanγ_coord_le
#check @scaledFan_not_stronglyCausalOn
#check @scaledFan_not_locallyStronglyCausal
#check @scaledFan_hasTimeFunction
#check @scaledFanγ_zero_snd
#check @scaledFanBelow
#check @scaledFan_not_causallyOpenFutureOn
#check @scaledFan_not_locallyCausallyOpenFuture
#check @scaledFan_separates
#check @not_locallyStronglyCausal_of_globallyHyperbolic_bare

#print axioms fanScale
#print axioms fanScale_pos
#print axioms fanScale_two_mul_le
#print axioms fanScale_zero
#print axioms fanScale_one
#print axioms combEps_zero
#print axioms combEps_one
#print axioms levelEmbed
#print axioms continuous_levelEmbed
#print axioms levelEmbed_injective
#print axioms scaledFanArc
#print axioms scaledFanSet
#print axioms scaledFanγ
#print axioms scaledFanA
#print axioms scaledFan
#print axioms continuous_scaledFanγ
#print axioms scaledFanγ_val
#print axioms scaledFanγ_plane
#print axioms loopArc_snd_of_fst_eq_zero
#print axioms scaledFanArc_level_eq
#print axioms scaledFanγ_coherent
#print axioms scaledFan_le_iff
#print axioms scaledFanP_val
#print axioms scaledFanQ_val
#print axioms scaledFanPeak_val
#print axioms scaledFanA_val
#print axioms tendsto_scaledFanP
#print axioms tendsto_scaledFanQ
#print axioms abs_loopArc_fst_le
#print axioms loopArc_snd_mem
#print axioms scaledFanγ_coord_le
#print axioms scaledFan_not_stronglyCausalOn
#print axioms scaledFan_not_locallyStronglyCausal
#print axioms scaledFan_hasTimeFunction
#print axioms scaledFanγ_zero_snd
#print axioms scaledFanBelow
#print axioms scaledFan_not_causallyOpenFutureOn
#print axioms scaledFan_not_locallyCausallyOpenFuture
#print axioms scaledFan_separates
#print axioms not_locallyStronglyCausal_of_globallyHyperbolic_bare

-- the heart: globally hyperbolic and causally compact, not locally strongly causal, on the
-- ambient (T2, second countable), in either reading
example : T2Space scaledFanSet ∧ SecondCountableTopology scaledFanSet ∧
    (∀ W : Opens scaledFanSet, scaledFan.AbsolutelyMinimalOn W) ∧
    scaledFan.GloballyHyperbolic ∧ scaledFan.CausallyCompact ∧
    ¬ scaledFan.LocallyStronglyCausal := by
  obtain ⟨h1, h2, -, h4, -, -, -, -, h9, h10, -, -, -, -, h15, -⟩ := scaledFan_separates
  exact ⟨h1, h2, h4, h10, h9, h15⟩

-- the proposed [[fails]] entry's `from`, all at once, with the negated `to`
example : scaledFan.AbsolutelyMinimal ∧ scaledFan.CausallyArcConnected ∧ scaledFan.PushUp ∧
    scaledFan.LocallyPushUp ∧ scaledFan.IsCausal ∧ scaledFan.CausallyCompact ∧
    scaledFan.GloballyHyperbolic ∧ scaledFan.HasTimeFunction ∧ scaledFan.CurvesExtend ∧
    scaledFan.FutureOneConnected ∧ ¬ scaledFan.LocallyStronglyCausal := by
  obtain ⟨-, -, h3, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, h15, -⟩ := scaledFan_separates
  exact ⟨h3, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15⟩

-- the ladder read backwards: globally_hyperbolic ∧ tarentin ⇒ strongly_causal ⇒
-- locally_strongly_causal (T2)
example : ¬ scaledFan.Tarentin := by
  have hGH : scaledFan.GloballyHyperbolic :=
    scaledFanγ_coherent.globallyHyperbolic continuous_scaledFanγ
  have hN : ¬ scaledFan.LocallyStronglyCausal := scaledFan_not_locallyStronglyCausal
  intro hT
  exact hN (by causal_ladder)

-- level 0 is the linear copy (x, y) ↦ (x, x, y) of the loop fan
example (n : ℕ) (t : ℝ) :
    (scaledFanγ (0, n) t).val = ((loopγ n t).val.1, (loopγ n t).val.1, (loopγ n t).val.2) := by
  rw [scaledFanγ_val]
  simp only [levelEmbed, fanScale_zero, combEps_zero, one_mul]
  rfl

-- the contrast: the loop fan alone is locally strongly causal, the loop fan at every scale is not
example : loopFan.LocallyStronglyCausal ∧ ¬ scaledFan.LocallyStronglyCausal :=
  ⟨loopFan_locallyStronglyCausal, scaledFan_not_locallyStronglyCausal⟩

-- the strong form at `a`, and the bare corollary
example : ∀ W : Opens scaledFanSet, scaledFanA ∈ W → ¬ scaledFan.StronglyCausalOn W :=
  fun _ ha => scaledFan_not_stronglyCausalOn ha
