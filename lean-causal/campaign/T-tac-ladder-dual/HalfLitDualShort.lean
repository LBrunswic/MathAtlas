import Causal.HalfLitDual
import Causal.Ladder.Dual

/-! Scratch (T-tac-ladder-dual, not shipped): `halfLightLine_dual_separates_causallyOpenFuture`
(`Causal.HalfLitDual`) with the dual rules: the half-lit line's own facts in `have`s, no `dual_*`
transport, one `causal_ladder` per conjunct. Typecheck with `lake env lean` from lean-causal/. -/

open Causal

example :
    halfLightLine.dual.AbsolutelyMinimal ∧ halfLightLine.dual.CausallyArcConnected ∧
      halfLightLine.dual.PushUp ∧ halfLightLine.dual.LocallyPushUp ∧
      halfLightLine.dual.IsCausal ∧ halfLightLine.dual.GloballyHyperbolic ∧
      halfLightLine.dual.CausallyCompact ∧ halfLightLine.dual.StronglyCausalOpen ∧
      halfLightLine.dual.StronglyCausal ∧ halfLightLine.dual.HasTimeFunction ∧
      halfLightLine.dual.CurvesExtend ∧
      ¬ halfLightLine.dual.CausallyOpenFuture ∧ ¬ halfLightLine.dual.LocallyCausallyOpenFuture ∧
      ¬ halfLightLine.dual.CausallyOpen ∧ ¬ halfLightLine.dual.LocallyCausallyOpen ∧
      ¬ halfLightLine.dual.Tarentin ∧ ¬ halfLightLine.dual.ChronalNeighbours ∧
      ¬ halfLightLine.dual.CausallyPlain := by
  have := halfLightLine_absolutelyMinimal
  have := halfLightLine_causallyArcConnected
  have := halfLightLine_globallyHyperbolic
  have := halfLightLine_pushUp
  have := halfLightLine_stronglyCausalOpen
  have := halfLightLine_hasTimeFunction
  have hNCOF := halfLightLine_not_causallyOpenPast
  exact ⟨by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder,
    by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder,
    by causal_ladder, hNCOF, fun _ => hNCOF (by causal_ladder), fun _ => hNCOF (by causal_ladder),
    fun _ => hNCOF (by causal_ladder), fun _ => halfLightLine_not_tarentin (by causal_ladder),
    fun _ => halfLightLine_not_chronalNeighbours (by causal_ladder),
    fun _ => halfLightLine_not_causallyPlain (by causal_ladder)⟩
