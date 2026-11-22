import Causal.Ladder.Rules
import Causal.Ladder.Dual
import Causal.ArcConnected
import Causal.CauchyExtension
import Causal.CurvesExtend
import Causal.Generated
import Causal.LadderLocal
import Causal.Properties

-- scratch (T-tac-ladder-dual): every single-premise cross pair, derived or not

section
universe u
variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M)

-- derived is_causal(C) ⇒ is_causal(C.dual)
example (_h0 : Causal.Causality.IsCausal C) : Causal.Causality.IsCausal C.dual := by causal_ladder
-- derived is_causal(C.dual) ⇒ is_causal(C)
example (_h0 : Causal.Causality.IsCausal C.dual) : Causal.Causality.IsCausal C := by causal_ladder
-- derived strongly_causal(C) ⇒ strongly_causal(C.dual)
example (_h0 : Causal.Causality.StronglyCausal C) : Causal.Causality.StronglyCausal C.dual := by causal_ladder
-- derived strongly_causal(C.dual) ⇒ strongly_causal(C)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : Causal.Causality.StronglyCausal C := by causal_ladder
-- derived strongly_causal_open(C) ⇒ strongly_causal(C.dual)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.StronglyCausal C.dual := by causal_ladder
-- derived strongly_causal_open(C) ⇒ strongly_causal_open(C.dual)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
-- derived strongly_causal_open(C.dual) ⇒ strongly_causal(C)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.StronglyCausal C := by causal_ladder
-- derived strongly_causal_open(C.dual) ⇒ strongly_causal_open(C)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.StronglyCausalOpen C := by causal_ladder
-- derived globally_hyperbolic(C) ⇒ is_causal(C.dual)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.IsCausal C.dual := by causal_ladder
-- derived globally_hyperbolic(C) ⇒ globally_hyperbolic(C.dual)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
-- derived globally_hyperbolic(C) ⇒ causally_compact(C.dual)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.CausallyCompact C.dual := by causal_ladder
-- derived globally_hyperbolic(C.dual) ⇒ is_causal(C)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.IsCausal C := by causal_ladder
-- derived globally_hyperbolic(C.dual) ⇒ globally_hyperbolic(C)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.GloballyHyperbolic C := by causal_ladder
-- derived globally_hyperbolic(C.dual) ⇒ causally_compact(C)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.CausallyCompact C := by causal_ladder
-- derived causally_compact(C) ⇒ causally_compact(C.dual)
example (_h0 : Causal.Causality.CausallyCompact C) : Causal.Causality.CausallyCompact C.dual := by causal_ladder
-- derived causally_compact(C.dual) ⇒ causally_compact(C)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : Causal.Causality.CausallyCompact C := by causal_ladder
-- derived push_up(C) ⇒ push_up(C.dual)
example (_h0 : Causal.Causality.PushUp C) : Causal.Causality.PushUp C.dual := by causal_ladder
-- derived push_up(C) ⇒ locally_push_up(C.dual)
example (_h0 : Causal.Causality.PushUp C) : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
-- derived push_up(C.dual) ⇒ push_up(C)
example (_h0 : Causal.Causality.PushUp C.dual) : Causal.Causality.PushUp C := by causal_ladder
-- derived push_up(C.dual) ⇒ locally_push_up(C)
example (_h0 : Causal.Causality.PushUp C.dual) : Causal.Causality.LocallyPushUp C := by causal_ladder
-- derived causally_open(C) ⇒ causally_open(C.dual)
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.CausallyOpen C.dual := by causal_ladder
-- derived causally_open(C) ⇒ causally_open_future(C.dual)
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
-- derived causally_open(C) ⇒ locally_causally_open_future(C.dual)
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
-- derived causally_open(C) ⇒ locally_causally_open(C.dual)
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
-- derived causally_open(C.dual) ⇒ causally_open(C)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.CausallyOpen C := by causal_ladder
-- derived causally_open(C.dual) ⇒ causally_open_future(C)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.CausallyOpenFuture C := by causal_ladder
-- derived causally_open(C.dual) ⇒ locally_causally_open_future(C)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
-- derived causally_open(C.dual) ⇒ locally_causally_open(C)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
-- derived absolutely_minimal(C) ⇒ absolutely_minimal(C.dual)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
-- derived absolutely_minimal(C.dual) ⇒ absolutely_minimal(C)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
-- derived causally_arc_connected(C) ⇒ absolutely_minimal(C.dual)
example (_h0 : Causal.Causality.CausallyArcConnected C) : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
-- derived causally_arc_connected(C) ⇒ causally_arc_connected(C.dual)
example (_h0 : Causal.Causality.CausallyArcConnected C) : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
-- derived causally_arc_connected(C.dual) ⇒ absolutely_minimal(C)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
-- derived causally_arc_connected(C.dual) ⇒ causally_arc_connected(C)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : Causal.Causality.CausallyArcConnected C := by causal_ladder
-- derived causally_plain(C) ⇒ causally_plain(C.dual)
example (_h0 : Causal.Causality.CausallyPlain C) : Causal.Causality.CausallyPlain C.dual := by causal_ladder
-- derived causally_plain(C.dual) ⇒ causally_plain(C)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : Causal.Causality.CausallyPlain C := by causal_ladder
-- derived tarentin(C) ⇒ tarentin(C.dual)
example (_h0 : Causal.Causality.Tarentin C) : Causal.Causality.Tarentin C.dual := by causal_ladder
-- derived tarentin(C.dual) ⇒ tarentin(C)
example (_h0 : Causal.Causality.Tarentin C.dual) : Causal.Causality.Tarentin C := by causal_ladder
-- derived time_function(C) ⇒ is_causal(C.dual)
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.IsCausal C.dual := by causal_ladder
-- derived time_function(C) ⇒ time_function(C.dual)
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
-- derived time_function(C) ⇒ curves_extend(C.dual)
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.CurvesExtend C.dual := by causal_ladder
-- derived time_function(C.dual) ⇒ is_causal(C)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.IsCausal C := by causal_ladder
-- derived time_function(C.dual) ⇒ time_function(C)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.HasTimeFunction C := by causal_ladder
-- derived time_function(C.dual) ⇒ curves_extend(C)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.CurvesExtend C := by causal_ladder
-- derived curves_extend(C) ⇒ curves_extend(C.dual)
example (_h0 : Causal.Causality.CurvesExtend C) : Causal.Causality.CurvesExtend C.dual := by causal_ladder
-- derived curves_extend(C.dual) ⇒ curves_extend(C)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : Causal.Causality.CurvesExtend C := by causal_ladder
-- derived locally_push_up(C) ⇒ locally_push_up(C.dual)
example (_h0 : Causal.Causality.LocallyPushUp C) : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
-- derived locally_push_up(C.dual) ⇒ locally_push_up(C)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : Causal.Causality.LocallyPushUp C := by causal_ladder
-- derived locally_causally_open(C) ⇒ locally_causally_open_future(C.dual)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
-- derived locally_causally_open(C) ⇒ locally_causally_open(C.dual)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
-- derived locally_causally_open(C.dual) ⇒ locally_causally_open_future(C)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
-- derived locally_causally_open(C.dual) ⇒ locally_causally_open(C)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
-- derived chronal_neighbours(C) ⇒ tarentin(C.dual)
example (_h0 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.Tarentin C.dual := by causal_ladder
-- derived chronal_neighbours(C) ⇒ chronal_neighbours(C.dual)
example (_h0 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
-- derived chronal_neighbours(C.dual) ⇒ tarentin(C)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.Tarentin C := by causal_ladder
-- derived chronal_neighbours(C.dual) ⇒ chronal_neighbours(C)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.ChronalNeighbours C := by causal_ladder
-- not derived is_causal(C) ⇏ strongly_causal(C.dual) (Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ strongly_causal_open(C.dual) (Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ push_up(C.dual) (Causal.deux_pushup)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ causally_arc_connected(C.dual) (Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ tarentin(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ time_function(C.dual) (Causal.fork_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ locally_causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ locally_causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ strongly_causal(C) (Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ strongly_causal_open(C) (Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ push_up(C) (Causal.deux_pushup)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ causally_arc_connected(C) (Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ tarentin(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ time_function(C) (Causal.fork_separates)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ locally_causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ locally_causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ push_up(C.dual) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ causally_arc_connected(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ causally_plain(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ tarentin(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ time_function(C.dual) (Causal.fork_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ locally_causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ locally_causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ chronal_neighbours(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ push_up(C) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ causally_arc_connected(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ causally_plain(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ tarentin(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ time_function(C) (Causal.fork_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ locally_causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ locally_causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ chronal_neighbours(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ push_up(C.dual) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ causally_arc_connected(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ causally_plain(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ tarentin(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ time_function(C.dual) (Causal.fork_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ locally_causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ locally_causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ chronal_neighbours(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ push_up(C) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ causally_arc_connected(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ causally_plain(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ tarentin(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ time_function(C) (Causal.fork_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ locally_causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ locally_causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ chronal_neighbours(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ strongly_causal(C.dual) (Causal.loopFan_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ strongly_causal_open(C.dual) (Causal.loopFan_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ push_up(C.dual) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ causally_open(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ causally_open_future(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ causally_arc_connected(C.dual) (Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ tarentin(C.dual) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ time_function(C.dual) (Causal.fork_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ locally_causally_open_future(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ locally_causally_open(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ strongly_causal(C) (Causal.loopFan_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ strongly_causal_open(C) (Causal.loopFan_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ push_up(C) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ causally_open(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ causally_open_future(C) (Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ causally_arc_connected(C) (Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ tarentin(C) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ time_function(C) (Causal.fork_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ locally_causally_open_future(C) (Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ locally_causally_open(C) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ globally_hyperbolic(C.dual) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ push_up(C.dual) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ causally_open(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ causally_open_future(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ causally_arc_connected(C.dual) (Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ tarentin(C.dual) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ locally_causally_open_future(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ locally_causally_open(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ globally_hyperbolic(C) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ push_up(C) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ causally_open(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ causally_open_future(C) (Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ causally_arc_connected(C) (Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ tarentin(C) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_zero_separates)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ locally_causally_open_future(C) (Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ locally_causally_open(C) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ absolutely_minimal(C.dual) (Causal.jumpLine_separates_causallyOpenFuture)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ causally_arc_connected(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ causally_plain(C.dual) (Causal.deux_pushup)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ tarentin(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ locally_causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ locally_causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ absolutely_minimal(C) (Causal.jumpLine_separates_causallyOpenFuture)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ causally_arc_connected(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ causally_plain(C) (Causal.deux_pushup)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ tarentin(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ locally_causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ locally_causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ absolutely_minimal(C.dual) (Causal.globalLine_separates_tarentin)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ causally_arc_connected(C.dual) (Causal.globalLine_separates_tarentin)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ tarentin(C.dual) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ absolutely_minimal(C) (Causal.globalLine_separates_tarentin)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ causally_arc_connected(C) (Causal.globalLine_separates_tarentin)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ tarentin(C) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ push_up(C.dual) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ causally_open(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ causally_open_future(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ causally_arc_connected(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ tarentin(C.dual) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ locally_causally_open_future(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ locally_causally_open(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ push_up(C) (Causal.gateLine_separates_pushUp, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ causally_open(C) (Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ causally_open_future(C) (Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ causally_arc_connected(C) (Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ tarentin(C) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ locally_causally_open_future(C) (Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ locally_causally_open(C) (Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ causally_arc_connected(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ tarentin(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ locally_causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ locally_causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ causally_arc_connected(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ tarentin(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ locally_causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ locally_causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ causally_open(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ causally_open_future(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ tarentin(C.dual) (Causal.tarentin_and_plain_needed)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ locally_causally_open_future(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ locally_causally_open(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ causally_open(C) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ causally_open_future(C) (Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ tarentin(C) (Causal.tarentin_and_plain_needed)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ locally_causally_open_future(C) (Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ locally_causally_open(C) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ globally_hyperbolic(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ causally_compact(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ push_up(C.dual) (Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ causally_open(C.dual) (Causal.notchedCausality_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ causally_open_future(C.dual) (Causal.notchedCausality_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ absolutely_minimal(C.dual) (Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ causally_arc_connected(C.dual) (Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ tarentin(C.dual) (Causal.tarentin_and_plain_needed)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ locally_causally_open_future(C.dual) (Causal.notchedCausality_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ locally_causally_open(C.dual) (Causal.notchedCausality_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ chronal_neighbours(C.dual) (Causal.tarentin_and_plain_needed)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ globally_hyperbolic(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ causally_compact(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ push_up(C) (Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ causally_open(C) (Causal.notchedCausality_separates)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ causally_open_future(C) (Causal.notchedCausality_separates, time-reversed)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ absolutely_minimal(C) (Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ causally_arc_connected(C) (Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ tarentin(C) (Causal.tarentin_and_plain_needed)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ locally_causally_open_future(C) (Causal.notchedCausality_separates, time-reversed)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ locally_causally_open(C) (Causal.notchedCausality_separates)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ chronal_neighbours(C) (Causal.tarentin_and_plain_needed)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ causally_open(C.dual) (Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ causally_open_future(C.dual) (Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ absolutely_minimal(C.dual) (Causal.globalLine_separates_tarentin)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ causally_arc_connected(C.dual) (Causal.globalLine_separates_tarentin)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ locally_causally_open_future(C.dual) (Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ locally_causally_open(C.dual) (Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ causally_open(C) (Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ causally_open_future(C) (Causal.oneWayMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ absolutely_minimal(C) (Causal.globalLine_separates_tarentin)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ causally_arc_connected(C) (Causal.globalLine_separates_tarentin)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ locally_causally_open_future(C) (Causal.oneWayMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ locally_causally_open(C) (Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ strongly_causal(C.dual) (Causal.loopFan_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ strongly_causal_open(C.dual) (Causal.loopFan_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ absolutely_minimal(C.dual) (Causal.jumpLine_separates_causallyOpenFuture)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ causally_arc_connected(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ causally_plain(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ tarentin(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ locally_causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ locally_causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived time_function(C) ⇏ chronal_neighbours(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ strongly_causal(C) (Causal.loopFan_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ strongly_causal_open(C) (Causal.loopFan_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ absolutely_minimal(C) (Causal.jumpLine_separates_causallyOpenFuture)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ causally_arc_connected(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ causally_plain(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ tarentin(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ locally_causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ locally_causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived time_function(C.dual) ⇏ chronal_neighbours(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ strongly_causal(C.dual) (Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ strongly_causal_open(C.dual) (Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ push_up(C.dual) (Causal.deux_pushup)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ causally_arc_connected(C.dual) (Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ tarentin(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ locally_causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ locally_causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ strongly_causal(C) (Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ strongly_causal_open(C) (Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ push_up(C) (Causal.deux_pushup)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ causally_arc_connected(C) (Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ tarentin(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ locally_causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ locally_causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived curves_extend(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ push_up(C.dual) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ causally_arc_connected(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ causally_plain(C.dual) (Causal.deux_pushup)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ tarentin(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ locally_causally_open_future(C.dual) (Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ locally_causally_open(C.dual) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ push_up(C) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ causally_arc_connected(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ causally_plain(C) (Causal.deux_pushup)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ tarentin(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ locally_causally_open_future(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ locally_causally_open(C) (Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ push_up(C.dual) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ causally_open(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ causally_open_future(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ causally_arc_connected(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ tarentin(C.dual) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ locally_causally_open_future(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ locally_causally_open(C.dual) (Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ push_up(C) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ causally_open(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ causally_open_future(C) (Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ causally_arc_connected(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ tarentin(C) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ locally_causally_open_future(C) (Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ locally_causally_open(C) (Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ push_up(C.dual) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ causally_open(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ causally_open_future(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ absolutely_minimal(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ causally_arc_connected(C.dual) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ causally_plain(C.dual) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ tarentin(C.dual) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ locally_push_up(C.dual) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ chronal_neighbours(C.dual) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ push_up(C) (Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ causally_open(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ causally_open_future(C) (Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ absolutely_minimal(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ causally_arc_connected(C) (Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ causally_plain(C) (Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ tarentin(C) (Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ locally_push_up(C) (Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ chronal_neighbours(C) (Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ is_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ strongly_causal(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ strongly_causal_open(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ globally_hyperbolic(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ causally_compact(C.dual) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ push_up(C.dual) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ causally_open(C.dual) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ causally_open_future(C.dual) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ causally_arc_connected(C.dual) (Causal.rationalJumpPlane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ causally_plain(C.dual) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ time_function(C.dual) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ locally_push_up(C.dual) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ locally_causally_open_future(C.dual) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ locally_causally_open(C.dual) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ is_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ strongly_causal(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ strongly_causal_open(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ globally_hyperbolic(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ causally_compact(C) (Causal.halfPlane_hypotheses)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ push_up(C) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ causally_open(C) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ causally_open_future(C) (Causal.chronalMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ causally_arc_connected(C) (Causal.rationalJumpPlane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ causally_plain(C) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ time_function(C) (Causal.Flat.timeCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ locally_push_up(C) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ locally_causally_open_future(C) (Causal.chronalMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ locally_causally_open(C) (Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- not derived is_causal(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived is_causal(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ is_causal(C.dual) (unknown)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ strongly_causal_open(C.dual) (unknown)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ is_causal(C) (unknown)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ strongly_causal_open(C) (unknown)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- not derived strongly_causal(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ is_causal(C.dual) (unknown)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ is_causal(C) (unknown)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- not derived strongly_causal_open(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived globally_hyperbolic(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived causally_compact(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived causally_compact(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived push_up(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived push_up(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived causally_open(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived causally_open(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived causally_open_future(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived causally_open_future(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived absolutely_minimal(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived absolutely_minimal(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived causally_arc_connected(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived causally_arc_connected(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C) ⇏ locally_push_up(C.dual) (unknown)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived causally_plain(C.dual) ⇏ locally_push_up(C) (unknown)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- not derived tarentin(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived tarentin(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived locally_push_up(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived locally_push_up(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open_future(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived locally_causally_open(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived locally_causally_open(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ absolutely_minimal(C.dual) (unknown)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- not derived chronal_neighbours(C) ⇏ curves_extend(C.dual) (unknown)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ absolutely_minimal(C) (unknown)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- not derived chronal_neighbours(C.dual) ⇏ curves_extend(C) (unknown)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial

end
