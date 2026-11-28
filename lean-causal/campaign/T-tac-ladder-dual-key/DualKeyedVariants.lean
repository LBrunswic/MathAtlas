import Causal.Ladder.Basic
import Causal.ArcConnected
import Causal.CausallyPlainLocZ
import Causal.ChronalNeighbourBridge
import Causal.ChronalTarentin
import Causal.CurvesExtend
import Causal.CurvesExtendSecondCountable
import Causal.DeuxPushup
import Causal.DiamondConfinement
import Causal.GlobalHyperbolicity
import Causal.LadderLocal
import Causal.LevinTimeFunction
import Causal.Properties
import Causal.PushUpOfMinimalLocal
import Causal.StrongCausality
import Causal.StrongCausalityHull
import Causal.CauchyExtension
import Causal.Generated
import Causal.InextensibleNestedBasics
import Causal.Minimal
import Causal.NestedCausalities
import Causal.NestedConverse
import Causal.PushUp
import Causal.TimelikeHomotopy

-- scratch (T-tac-ladder-dual-key): the edge rules of Causal.Ladder.Rules (emit_lean), the dual
-- rules emit_dual generates from the keyed copy of the ladder, and their tests; the hand-written
-- Causal.Ladder.Dual is not imported, directly or transitively.


-- strongly_causal ⇒ is_causal (standing: T1)
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.StronglyCausal.isCausal
-- strongly_causal ∧ causally_open ⇒ strongly_causal_open
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.StronglyCausal.stronglyCausalOpen_of_causallyOpen
-- strongly_causal_open ⇒ strongly_causal
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.StronglyCausalOpen.stronglyCausal
-- globally_hyperbolic ∧ tarentin ⇒ strongly_causal (standing: T2)
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.GloballyHyperbolic.stronglyCausal
-- causally_arc_connected ⇒ absolutely_minimal
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.CausallyArcConnected.absolutelyMinimal
-- causally_arc_connected ∧ locally_push_up ⇒ push_up
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.CausallyArcConnected.pushUp_of_locallyPushUp
-- absolutely_minimal ∧ locally_push_up ⇒ push_up (standing: T1)
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.AbsolutelyMinimal.pushUp_of_locallyPushUp
-- absolutely_minimal ∧ causally_plain ⇒ push_up (standing: T1)
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.pushUp_of_causallyPlain_of_absolutelyMinimal
-- push_up ∧ chronal_neighbours ⇒ causally_open
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.PushUp.causallyOpen_of_chronalNeighbours
-- push_up ∧ chronal_neighbours ⇒ causally_plain
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.PushUp.causallyPlain_of_chronalNeighbours
-- chronal_neighbours ⇒ tarentin
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.ChronalNeighbours.tarentin
-- chronal_neighbours ⇒ has_chronal_neighbour
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.ChronalNeighbours.hasChronalNeighbourEverywhere
-- absolutely_minimal ∧ locally_causally_open_future ⇒ causally_open_future
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture
-- absolutely_minimal ∧ locally_causally_open ⇒ causally_open
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.AbsolutelyMinimal.causallyOpen_of_locallyCausallyOpen
-- causally_open ⇒ causally_open_future
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.CausallyOpen.future
-- globally_hyperbolic ⇒ is_causal
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.GloballyHyperbolic.isCausal
-- globally_hyperbolic ⇒ causally_compact
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.GloballyHyperbolic.causallyCompact
-- is_causal ∧ causally_compact ⇒ globally_hyperbolic
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.IsCausal.globallyHyperbolic
-- push_up ⇒ locally_push_up
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.PushUp.locallyPushUp
-- causally_open_future ⇒ locally_causally_open_future
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.CausallyOpenFuture.locallyCausallyOpenFuture
-- causally_open ⇒ locally_causally_open
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.CausallyOpen.locallyCausallyOpen
-- locally_causally_open ⇒ locally_causally_open_future
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.LocallyCausallyOpen.future
-- strongly_causal ⇒ locally_strongly_causal
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.StronglyCausal.locallyStronglyCausal
-- time_function ⇒ curves_extend
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.HasTimeFunction.curvesExtend
-- time_function ⇒ is_causal
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.HasTimeFunction.isCausal
-- globally_hyperbolic ∧ tarentin ⇒ time_function (standing: T2, second_countable)
attribute [aesop safe forward (rule_sets := [CausalLadder])] Causal.Causality.GloballyHyperbolic.hasTimeFunction
-- fact: curves_extend (standing: T1, second_countable)
attribute [aesop safe apply (rule_sets := [CausalLadder])] Causal.Causality.curvesExtend_of_t1_secondCountable

-- skipped Causal.Causality.LeNested.curveNestedOn (le_nested ⇒ curve_nested): sort: joins a property not of the sort causality
-- skipped Causal.Causality.InextensibleNestedOn.curveNestedOn_of_t1_secondCountable (inextensible_nested ⇒ curve_nested): sort: joins a property not of the sort causality
-- skipped fact Causal.CBG.eqOn_of_liftPropOn (rigid): sort: rigid is not of the sort causality

namespace Causal.LadderDual

universe u

variable {M : Type u} [TopologicalSpace M] {C C' : Causal.Causality M} {W : TopologicalSpace.Opens M}

/-! ## Two-sided nodes: `P C.dual → P C` and `P C → P C.dual` -/

-- is_causal: Causal.Causality.dual_isCausal (an iff)
theorem isCausal_of_dual (h : Causal.Causality.IsCausal C.dual) : Causal.Causality.IsCausal C :=
  Causal.Causality.dual_isCausal.1 h
theorem isCausal_dual (h : Causal.Causality.IsCausal C) : Causal.Causality.IsCausal C.dual :=
  Causal.Causality.dual_isCausal.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] isCausal_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] isCausal_dual

-- strongly_causal: Causal.Causality.dual_stronglyCausal (an iff)
theorem stronglyCausal_of_dual (h : Causal.Causality.StronglyCausal C.dual) : Causal.Causality.StronglyCausal C :=
  Causal.Causality.dual_stronglyCausal.1 h
theorem stronglyCausal_dual (h : Causal.Causality.StronglyCausal C) : Causal.Causality.StronglyCausal C.dual :=
  Causal.Causality.dual_stronglyCausal.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] stronglyCausal_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] stronglyCausal_dual

-- strongly_causal_open: Causal.Causality.dual_stronglyCausalOpen (an iff)
theorem stronglyCausalOpen_of_dual (h : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.StronglyCausalOpen C :=
  Causal.Causality.dual_stronglyCausalOpen.1 h
theorem stronglyCausalOpen_dual (h : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.StronglyCausalOpen C.dual :=
  Causal.Causality.dual_stronglyCausalOpen.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] stronglyCausalOpen_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] stronglyCausalOpen_dual

-- globally_hyperbolic: Causal.Causality.dual_globallyHyperbolic (an iff)
theorem globallyHyperbolic_of_dual (h : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.GloballyHyperbolic C :=
  Causal.Causality.dual_globallyHyperbolic.1 h
theorem globallyHyperbolic_dual (h : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.GloballyHyperbolic C.dual :=
  Causal.Causality.dual_globallyHyperbolic.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] globallyHyperbolic_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] globallyHyperbolic_dual

-- causally_compact: Causal.Causality.dual_causallyCompact (an iff)
theorem causallyCompact_of_dual (h : Causal.Causality.CausallyCompact C.dual) : Causal.Causality.CausallyCompact C :=
  Causal.Causality.dual_causallyCompact.1 h
theorem causallyCompact_dual (h : Causal.Causality.CausallyCompact C) : Causal.Causality.CausallyCompact C.dual :=
  Causal.Causality.dual_causallyCompact.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] causallyCompact_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] causallyCompact_dual

-- push_up: Causal.Causality.dual_pushUp (an iff)
theorem pushUp_of_dual (h : Causal.Causality.PushUp C.dual) : Causal.Causality.PushUp C :=
  Causal.Causality.dual_pushUp.1 h
theorem pushUp_dual (h : Causal.Causality.PushUp C) : Causal.Causality.PushUp C.dual :=
  Causal.Causality.dual_pushUp.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] pushUp_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] pushUp_dual

-- causally_open: Causal.Causality.dual_causallyOpen (an iff)
theorem causallyOpen_of_dual (h : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.CausallyOpen C :=
  Causal.Causality.dual_causallyOpen.1 h
theorem causallyOpen_dual (h : Causal.Causality.CausallyOpen C) : Causal.Causality.CausallyOpen C.dual :=
  Causal.Causality.dual_causallyOpen.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] causallyOpen_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] causallyOpen_dual

-- absolutely_minimal: Causal.Causality.dual_absolutelyMinimal (an iff)
theorem absolutelyMinimal_of_dual (h : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : Causal.Precausality.AbsolutelyMinimal C.toPrecausality :=
  Causal.Causality.dual_absolutelyMinimal.1 h
theorem absolutelyMinimal_dual (h : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality :=
  Causal.Causality.dual_absolutelyMinimal.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] absolutelyMinimal_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] absolutelyMinimal_dual

-- causally_arc_connected: Causal.Causality.dual_causallyArcConnectedOn (an iff)
theorem causallyArcConnected_of_dual (h : Causal.Causality.CausallyArcConnected C.dual) : Causal.Causality.CausallyArcConnected C :=
  Causal.Causality.dual_causallyArcConnectedOn.1 h
theorem causallyArcConnected_dual (h : Causal.Causality.CausallyArcConnected C) : Causal.Causality.CausallyArcConnected C.dual :=
  Causal.Causality.dual_causallyArcConnectedOn.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] causallyArcConnected_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] causallyArcConnected_dual

-- causally_plain: Causal.Causality.dual_causallyPlain (an iff)
theorem causallyPlain_of_dual (h : Causal.Causality.CausallyPlain C.dual) : Causal.Causality.CausallyPlain C :=
  Causal.Causality.dual_causallyPlain.1 h
theorem causallyPlain_dual (h : Causal.Causality.CausallyPlain C) : Causal.Causality.CausallyPlain C.dual :=
  Causal.Causality.dual_causallyPlain.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] causallyPlain_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] causallyPlain_dual

-- tarentin: Causal.Causality.dual_tarentin (an iff)
theorem tarentin_of_dual (h : Causal.Causality.Tarentin C.dual) : Causal.Causality.Tarentin C :=
  Causal.Causality.dual_tarentin.1 h
theorem tarentin_dual (h : Causal.Causality.Tarentin C) : Causal.Causality.Tarentin C.dual :=
  Causal.Causality.dual_tarentin.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] tarentin_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] tarentin_dual

-- time_function: Causal.Causality.dual_hasTimeFunction (an iff)
theorem hasTimeFunction_of_dual (h : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.HasTimeFunction C :=
  Causal.Causality.dual_hasTimeFunction.1 h
theorem hasTimeFunction_dual (h : Causal.Causality.HasTimeFunction C) : Causal.Causality.HasTimeFunction C.dual :=
  Causal.Causality.dual_hasTimeFunction.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] hasTimeFunction_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] hasTimeFunction_dual

-- curves_extend: Causal.Causality.CurvesExtend.dual (an implication, read at C and at C.dual)
theorem curvesExtend_of_dual (h : Causal.Causality.CurvesExtend C.dual) : Causal.Causality.CurvesExtend C :=
  (Causal.Causality.CurvesExtend.dual h :)
theorem curvesExtend_dual (h : Causal.Causality.CurvesExtend C) : Causal.Causality.CurvesExtend C.dual :=
  Causal.Causality.CurvesExtend.dual h
attribute [aesop safe forward (rule_sets := [CausalLadder])] curvesExtend_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] curvesExtend_dual

-- locally_push_up: Causal.Causality.dual_locallyPushUp (an iff)
theorem locallyPushUp_of_dual (h : Causal.Causality.LocallyPushUp C.dual) : Causal.Causality.LocallyPushUp C :=
  Causal.Causality.dual_locallyPushUp.1 h
theorem locallyPushUp_dual (h : Causal.Causality.LocallyPushUp C) : Causal.Causality.LocallyPushUp C.dual :=
  Causal.Causality.dual_locallyPushUp.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] locallyPushUp_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] locallyPushUp_dual

-- locally_causally_open: Causal.Causality.dual_locallyCausallyOpen (an iff)
theorem locallyCausallyOpen_of_dual (h : Causal.Causality.LocallyCausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpen C :=
  Causal.Causality.dual_locallyCausallyOpen.1 h
theorem locallyCausallyOpen_dual (h : Causal.Causality.LocallyCausallyOpen C) : Causal.Causality.LocallyCausallyOpen C.dual :=
  Causal.Causality.dual_locallyCausallyOpen.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] locallyCausallyOpen_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] locallyCausallyOpen_dual

-- chronal_neighbours: Causal.Causality.dual_chronalNeighbours (an iff)
theorem chronalNeighbours_of_dual (h : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.ChronalNeighbours C :=
  Causal.Causality.dual_chronalNeighbours.1 h
theorem chronalNeighbours_dual (h : Causal.Causality.ChronalNeighbours C) : Causal.Causality.ChronalNeighbours C.dual :=
  Causal.Causality.dual_chronalNeighbours.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] chronalNeighbours_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] chronalNeighbours_dual

-- has_chronal_neighbour: Causal.Causality.dual_hasChronalNeighbourEverywhere (an iff)
theorem hasChronalNeighbourEverywhere_of_dual (h : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : Causal.Causality.HasChronalNeighbourEverywhere C :=
  Causal.Causality.dual_hasChronalNeighbourEverywhere.1 h
theorem hasChronalNeighbourEverywhere_dual (h : Causal.Causality.HasChronalNeighbourEverywhere C) : Causal.Causality.HasChronalNeighbourEverywhere C.dual :=
  Causal.Causality.dual_hasChronalNeighbourEverywhere.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] hasChronalNeighbourEverywhere_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] hasChronalNeighbourEverywhere_dual

-- future_one_connected: Causal.Causality.dual_futureOneConnected (an iff)
theorem futureOneConnected_of_dual (h : Causal.Causality.FutureOneConnected C.dual) : Causal.Causality.FutureOneConnected C :=
  Causal.Causality.dual_futureOneConnected.1 h
theorem futureOneConnected_dual (h : Causal.Causality.FutureOneConnected C) : Causal.Causality.FutureOneConnected C.dual :=
  Causal.Causality.dual_futureOneConnected.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] futureOneConnected_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] futureOneConnected_dual

-- locally_strongly_causal: Causal.Causality.dual_locallyStronglyCausal (an iff)
theorem locallyStronglyCausal_of_dual (h : Causal.Causality.LocallyStronglyCausal C.dual) : Causal.Causality.LocallyStronglyCausal C :=
  Causal.Causality.dual_locallyStronglyCausal.1 h
theorem locallyStronglyCausal_dual (h : Causal.Causality.LocallyStronglyCausal C) : Causal.Causality.LocallyStronglyCausal C.dual :=
  Causal.Causality.dual_locallyStronglyCausal.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] locallyStronglyCausal_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] locallyStronglyCausal_dual

/-! ## One-sided nodes: the two-sided node from the future and the past forms -/

-- causally_open_future introduces causally_open: Causal.Causality.CausallyOpen (the definition of the two-sided node)
theorem causallyOpen_of_future_of_past (hf : Causal.Causality.CausallyOpenFuture C) (hp : Causal.Causality.CausallyOpenFuture C.dual) : Causal.Causality.CausallyOpen C :=
  ⟨hf, hp⟩
attribute [aesop safe forward (rule_sets := [CausalLadder])] causallyOpen_of_future_of_past

-- locally_causally_open_future introduces locally_causally_open: Causal.Causality.LocallyCausallyOpen (the definition of the two-sided node)
theorem locallyCausallyOpen_of_future_of_past (hf : Causal.Causality.LocallyCausallyOpenFuture C) (hp : Causal.Causality.LocallyCausallyOpenFuture C.dual) : Causal.Causality.LocallyCausallyOpen C :=
  ⟨hf, hp⟩
attribute [aesop safe forward (rule_sets := [CausalLadder])] locallyCausallyOpen_of_future_of_past

/-! ## Pair nodes: both causalities reversed, the pattern on the first -/

-- le_nested: Causal.Causality.dual_leNested_iff (an iff)
theorem leNested_of_dual (h : Causal.Causality.LeNested C.dual C'.dual) : Causal.Causality.LeNested C C' :=
  Causal.Causality.dual_leNested_iff.1 h
theorem leNested_dual (h : Causal.Causality.LeNested C C') : Causal.Causality.LeNested C.dual C'.dual :=
  Causal.Causality.dual_leNested_iff.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] leNested_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] leNested_dual

-- curve_nested: Causal.Causality.CurveNestedOn.dual (an implication, read at C and at C.dual)
theorem curveNestedOn_of_dual (h : Causal.Causality.CurveNestedOn C.dual C'.dual W) : Causal.Causality.CurveNestedOn C C' W :=
  (Causal.Causality.CurveNestedOn.dual h :)
theorem curveNestedOn_dual (h : Causal.Causality.CurveNestedOn C C' W) : Causal.Causality.CurveNestedOn C.dual C'.dual W :=
  Causal.Causality.CurveNestedOn.dual h
attribute [aesop safe forward (rule_sets := [CausalLadder])] curveNestedOn_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] curveNestedOn_dual

-- inextensible_nested: Causal.Causality.InextensibleNestedOn.dual (an implication, read at C and at C.dual)
theorem inextensibleNestedOn_of_dual (h : Causal.Causality.InextensibleNestedOn C.dual C'.dual W) : Causal.Causality.InextensibleNestedOn C C' W :=
  (Causal.Causality.InextensibleNestedOn.dual h :)
theorem inextensibleNestedOn_dual (h : Causal.Causality.InextensibleNestedOn C C' W) : Causal.Causality.InextensibleNestedOn C.dual C'.dual W :=
  Causal.Causality.InextensibleNestedOn.dual h
attribute [aesop safe forward (rule_sets := [CausalLadder])] inextensibleNestedOn_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] inextensibleNestedOn_dual

end Causal.LadderDual

open Lean in
run_cmd do
  let models : List Name := [`Causal.Minkowski, `Causal.Static, `Causal.SingularFlat, `Causal.Flat, `Causal.Model, `Causal.Port]
  for m in (← getEnv).header.moduleNames do
    if models.any (·.isPrefixOf m) then
      throwError "the ladder's Lean imports the model module {m}"

section

universe u

variable {M : Type u} [TopologicalSpace M] (C C' : Causal.Causality M)

/-! ## Derived across time reversal, from one property -/

-- is_causal(C) ⇒ is_causal(C.dual)
example (_h0 : Causal.Causality.IsCausal C) : Causal.Causality.IsCausal C.dual := by causal_ladder
-- is_causal(C.dual) ⇒ is_causal(C)
example (_h0 : Causal.Causality.IsCausal C.dual) : Causal.Causality.IsCausal C := by causal_ladder
-- strongly_causal(C) ⇒ strongly_causal(C.dual)
example (_h0 : Causal.Causality.StronglyCausal C) : Causal.Causality.StronglyCausal C.dual := by causal_ladder
-- strongly_causal(C) ⇒ locally_strongly_causal(C.dual)
example (_h0 : Causal.Causality.StronglyCausal C) : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
-- strongly_causal(C.dual) ⇒ strongly_causal(C)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : Causal.Causality.StronglyCausal C := by causal_ladder
-- strongly_causal(C.dual) ⇒ locally_strongly_causal(C)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
-- strongly_causal_open(C) ⇒ strongly_causal(C.dual)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.StronglyCausal C.dual := by causal_ladder
-- strongly_causal_open(C) ⇒ strongly_causal_open(C.dual)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
-- strongly_causal_open(C) ⇒ locally_strongly_causal(C.dual)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
-- strongly_causal_open(C.dual) ⇒ strongly_causal(C)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.StronglyCausal C := by causal_ladder
-- strongly_causal_open(C.dual) ⇒ strongly_causal_open(C)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.StronglyCausalOpen C := by causal_ladder
-- strongly_causal_open(C.dual) ⇒ locally_strongly_causal(C)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
-- globally_hyperbolic(C) ⇒ is_causal(C.dual)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.IsCausal C.dual := by causal_ladder
-- globally_hyperbolic(C) ⇒ globally_hyperbolic(C.dual)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
-- globally_hyperbolic(C) ⇒ causally_compact(C.dual)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.CausallyCompact C.dual := by causal_ladder
-- globally_hyperbolic(C.dual) ⇒ is_causal(C)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.IsCausal C := by causal_ladder
-- globally_hyperbolic(C.dual) ⇒ globally_hyperbolic(C)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.GloballyHyperbolic C := by causal_ladder
-- globally_hyperbolic(C.dual) ⇒ causally_compact(C)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.CausallyCompact C := by causal_ladder
-- causally_compact(C) ⇒ causally_compact(C.dual)
example (_h0 : Causal.Causality.CausallyCompact C) : Causal.Causality.CausallyCompact C.dual := by causal_ladder
-- causally_compact(C.dual) ⇒ causally_compact(C)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : Causal.Causality.CausallyCompact C := by causal_ladder
-- push_up(C) ⇒ push_up(C.dual)
example (_h0 : Causal.Causality.PushUp C) : Causal.Causality.PushUp C.dual := by causal_ladder
-- push_up(C) ⇒ locally_push_up(C.dual)
example (_h0 : Causal.Causality.PushUp C) : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
-- push_up(C.dual) ⇒ push_up(C)
example (_h0 : Causal.Causality.PushUp C.dual) : Causal.Causality.PushUp C := by causal_ladder
-- push_up(C.dual) ⇒ locally_push_up(C)
example (_h0 : Causal.Causality.PushUp C.dual) : Causal.Causality.LocallyPushUp C := by causal_ladder
-- causally_open(C) ⇒ causally_open(C.dual)
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.CausallyOpen C.dual := by causal_ladder
-- causally_open(C) ⇒ causally_open_future(C.dual)
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
-- causally_open(C) ⇒ locally_causally_open_future(C.dual)
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
-- causally_open(C) ⇒ locally_causally_open(C.dual)
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
-- causally_open(C.dual) ⇒ causally_open(C)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.CausallyOpen C := by causal_ladder
-- causally_open(C.dual) ⇒ causally_open_future(C)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.CausallyOpenFuture C := by causal_ladder
-- causally_open(C.dual) ⇒ locally_causally_open_future(C)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
-- causally_open(C.dual) ⇒ locally_causally_open(C)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
-- absolutely_minimal(C) ⇒ absolutely_minimal(C.dual)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
-- absolutely_minimal(C.dual) ⇒ absolutely_minimal(C)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
-- causally_arc_connected(C) ⇒ absolutely_minimal(C.dual)
example (_h0 : Causal.Causality.CausallyArcConnected C) : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
-- causally_arc_connected(C) ⇒ causally_arc_connected(C.dual)
example (_h0 : Causal.Causality.CausallyArcConnected C) : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
-- causally_arc_connected(C.dual) ⇒ absolutely_minimal(C)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
-- causally_arc_connected(C.dual) ⇒ causally_arc_connected(C)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : Causal.Causality.CausallyArcConnected C := by causal_ladder
-- causally_plain(C) ⇒ causally_plain(C.dual)
example (_h0 : Causal.Causality.CausallyPlain C) : Causal.Causality.CausallyPlain C.dual := by causal_ladder
-- causally_plain(C.dual) ⇒ causally_plain(C)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : Causal.Causality.CausallyPlain C := by causal_ladder
-- tarentin(C) ⇒ tarentin(C.dual)
example (_h0 : Causal.Causality.Tarentin C) : Causal.Causality.Tarentin C.dual := by causal_ladder
-- tarentin(C.dual) ⇒ tarentin(C)
example (_h0 : Causal.Causality.Tarentin C.dual) : Causal.Causality.Tarentin C := by causal_ladder
-- time_function(C) ⇒ is_causal(C.dual)
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.IsCausal C.dual := by causal_ladder
-- time_function(C) ⇒ time_function(C.dual)
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
-- time_function(C) ⇒ curves_extend(C.dual)
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.CurvesExtend C.dual := by causal_ladder
-- time_function(C.dual) ⇒ is_causal(C)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.IsCausal C := by causal_ladder
-- time_function(C.dual) ⇒ time_function(C)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.HasTimeFunction C := by causal_ladder
-- time_function(C.dual) ⇒ curves_extend(C)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.CurvesExtend C := by causal_ladder
-- curves_extend(C) ⇒ curves_extend(C.dual)
example (_h0 : Causal.Causality.CurvesExtend C) : Causal.Causality.CurvesExtend C.dual := by causal_ladder
-- curves_extend(C.dual) ⇒ curves_extend(C)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : Causal.Causality.CurvesExtend C := by causal_ladder
-- locally_push_up(C) ⇒ locally_push_up(C.dual)
example (_h0 : Causal.Causality.LocallyPushUp C) : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
-- locally_push_up(C.dual) ⇒ locally_push_up(C)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : Causal.Causality.LocallyPushUp C := by causal_ladder
-- locally_causally_open(C) ⇒ locally_causally_open_future(C.dual)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
-- locally_causally_open(C) ⇒ locally_causally_open(C.dual)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
-- locally_causally_open(C.dual) ⇒ locally_causally_open_future(C)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
-- locally_causally_open(C.dual) ⇒ locally_causally_open(C)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
-- chronal_neighbours(C) ⇒ tarentin(C.dual)
example (_h0 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.Tarentin C.dual := by causal_ladder
-- chronal_neighbours(C) ⇒ chronal_neighbours(C.dual)
example (_h0 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
-- chronal_neighbours(C) ⇒ has_chronal_neighbour(C.dual)
example (_h0 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
-- chronal_neighbours(C.dual) ⇒ tarentin(C)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.Tarentin C := by causal_ladder
-- chronal_neighbours(C.dual) ⇒ chronal_neighbours(C)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.ChronalNeighbours C := by causal_ladder
-- chronal_neighbours(C.dual) ⇒ has_chronal_neighbour(C)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
-- has_chronal_neighbour(C) ⇒ has_chronal_neighbour(C.dual)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
-- has_chronal_neighbour(C.dual) ⇒ has_chronal_neighbour(C)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
-- future_one_connected(C) ⇒ future_one_connected(C.dual)
example (_h0 : Causal.Causality.FutureOneConnected C) : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
-- future_one_connected(C.dual) ⇒ future_one_connected(C)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : Causal.Causality.FutureOneConnected C := by causal_ladder
-- locally_strongly_causal(C) ⇒ locally_strongly_causal(C.dual)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
-- locally_strongly_causal(C.dual) ⇒ locally_strongly_causal(C)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : Causal.Causality.LocallyStronglyCausal C := by causal_ladder

/-! ## Derived on `C.dual` through a conjunctive rule, two-sided premises on `C` -/

-- strongly_causal(C) ∧ causally_open(C) ⇒ strongly_causal_open(C.dual) (Causal.Causality.StronglyCausal.stronglyCausalOpen_of_causallyOpen on C.dual)
example (_h0 : Causal.Causality.StronglyCausal C) (_h1 : Causal.Causality.CausallyOpen C) : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
-- causally_arc_connected(C) ∧ locally_push_up(C) ⇒ push_up(C.dual) (Causal.Causality.CausallyArcConnected.pushUp_of_locallyPushUp on C.dual)
example (_h0 : Causal.Causality.CausallyArcConnected C) (_h1 : Causal.Causality.LocallyPushUp C) : Causal.Causality.PushUp C.dual := by causal_ladder
-- push_up(C) ∧ chronal_neighbours(C) ⇒ causally_open(C.dual) (Causal.Causality.PushUp.causallyOpen_of_chronalNeighbours on C.dual)
example (_h0 : Causal.Causality.PushUp C) (_h1 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.CausallyOpen C.dual := by causal_ladder
-- push_up(C) ∧ chronal_neighbours(C) ⇒ causally_plain(C.dual) (Causal.Causality.PushUp.causallyPlain_of_chronalNeighbours on C.dual)
example (_h0 : Causal.Causality.PushUp C) (_h1 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.CausallyPlain C.dual := by causal_ladder
-- absolutely_minimal(C) ∧ locally_causally_open_future(C.dual) ⇒ causally_open_future(C.dual) (Causal.Causality.AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture on C.dual)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) (_h1 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
-- absolutely_minimal(C) ∧ locally_causally_open(C) ⇒ causally_open(C.dual) (Causal.Causality.AbsolutelyMinimal.causallyOpen_of_locallyCausallyOpen on C.dual)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) (_h1 : Causal.Causality.LocallyCausallyOpen C) : Causal.Causality.CausallyOpen C.dual := by causal_ladder
-- is_causal(C) ∧ causally_compact(C) ⇒ globally_hyperbolic(C.dual) (Causal.Causality.IsCausal.globallyHyperbolic on C.dual)
example (_h0 : Causal.Causality.IsCausal C) (_h1 : Causal.Causality.CausallyCompact C) : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder

/-! ## Introductions: the two-sided node from a one-sided node and its past form -/

-- causally_open_future(C) ∧ causally_open_future(C.dual) ⇒ causally_open(C) (causallyOpen_of_future_of_past)
example (_h0 : Causal.Causality.CausallyOpenFuture C) (_h1 : Causal.Causality.CausallyOpenFuture C.dual) : Causal.Causality.CausallyOpen C := by causal_ladder
-- causally_open_future(C) ∧ causally_open_future(C.dual) ⇒ causally_open(C.dual) (causallyOpen_of_future_of_past)
example (_h0 : Causal.Causality.CausallyOpenFuture C) (_h1 : Causal.Causality.CausallyOpenFuture C.dual) : Causal.Causality.CausallyOpen C.dual := by causal_ladder
-- locally_causally_open_future(C) ∧ locally_causally_open_future(C.dual) ⇒ locally_causally_open(C) (locallyCausallyOpen_of_future_of_past)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) (_h1 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
-- locally_causally_open_future(C) ∧ locally_causally_open_future(C.dual) ⇒ locally_causally_open(C.dual) (locallyCausallyOpen_of_future_of_past)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) (_h1 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder

/-! ## Pair nodes, both causalities reversed -/

-- le_nested(C, C') ⇒ le_nested(C.dual, C'.dual)
example (_h0 : Causal.Causality.LeNested C C') : Causal.Causality.LeNested C.dual C'.dual := by causal_ladder
-- le_nested(C.dual, C'.dual) ⇒ le_nested(C, C')
example (_h0 : Causal.Causality.LeNested C.dual C'.dual) : Causal.Causality.LeNested C C' := by causal_ladder
-- curve_nested(C, C') ⇒ curve_nested(C.dual, C'.dual)
example (W : TopologicalSpace.Opens M) (_h0 : Causal.Causality.CurveNestedOn C C' W) : Causal.Causality.CurveNestedOn C.dual C'.dual W := by causal_ladder
-- curve_nested(C.dual, C'.dual) ⇒ curve_nested(C, C')
example (W : TopologicalSpace.Opens M) (_h0 : Causal.Causality.CurveNestedOn C.dual C'.dual W) : Causal.Causality.CurveNestedOn C C' W := by causal_ladder
-- inextensible_nested(C, C') ⇒ inextensible_nested(C.dual, C'.dual)
example (W : TopologicalSpace.Opens M) (_h0 : Causal.Causality.InextensibleNestedOn C C' W) : Causal.Causality.InextensibleNestedOn C.dual C'.dual W := by causal_ladder
-- inextensible_nested(C.dual, C'.dual) ⇒ inextensible_nested(C, C')
example (W : TopologicalSpace.Opens M) (_h0 : Causal.Causality.InextensibleNestedOn C.dual C'.dual W) : Causal.Causality.InextensibleNestedOn C C' W := by causal_ladder

/-! ## Not derived across time reversal: refuted pairs -/

-- is_causal(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ push_up(C.dual) (refuted: Causal.deux_pushup)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- is_causal(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ time_function(C.dual) (refuted: Causal.fork_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- is_causal(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- is_causal(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- is_causal(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ causally_plain(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ time_function(C.dual) (refuted: Causal.fork_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- strongly_causal(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- strongly_causal(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- strongly_causal(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ causally_plain(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ time_function(C.dual) (refuted: Causal.fork_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- strongly_causal_open(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- strongly_causal_open(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ strongly_causal(C.dual) (refuted: Causal.loopFan_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.loopFan_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ causally_open(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ causally_open_future(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ tarentin(C.dual) (refuted: Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ time_function(C.dual) (refuted: Causal.fork_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.scaledFan_separates)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- globally_hyperbolic(C.dual) ⇏ causally_open_future(C) (refuted: Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- globally_hyperbolic(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- causally_compact(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_zero_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ strongly_causal(C.dual) (refuted: Causal.Flat.timeCylinder_zero_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.Flat.timeCylinder_zero_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.Flat.timeCylinder_zero_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ causally_open(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ causally_open_future(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- causally_compact(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.gateLine_not_absolutelyMinimalOn)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ tarentin(C.dual) (refuted: Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_zero_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- causally_compact(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.scaledFan_separates)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- causally_compact(C.dual) ⇏ causally_open_future(C) (refuted: Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- causally_compact(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- push_up(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.jumpLine_separates_causallyOpenFuture)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- push_up(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ causally_plain(C.dual) (refuted: Causal.deux_pushup)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- push_up(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- push_up(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- push_up(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- causally_open(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.globalLine_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- causally_open(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.globalLine_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ tarentin(C.dual) (refuted: Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- causally_open(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ causally_open(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ causally_open_future(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ tarentin(C.dual) (refuted: Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- causally_open_future(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ is_causal(C) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ strongly_causal(C) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ strongly_causal_open(C) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ globally_hyperbolic(C) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ causally_compact(C) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ push_up(C) (refuted: Causal.gateLine_separates_pushUp, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ causally_open(C) (refuted: Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ causally_open_future(C) (refuted: Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ absolutely_minimal(C) (refuted: Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ causally_arc_connected(C) (refuted: Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ causally_plain(C) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ tarentin(C) (refuted: Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ time_function(C) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ locally_push_up(C) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ locally_causally_open(C) (refuted: Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ chronal_neighbours(C) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ has_chronal_neighbour(C) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ future_one_connected(C) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- causally_open_future(C.dual) ⇏ locally_strongly_causal(C) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- absolutely_minimal(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- absolutely_minimal(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ causally_open(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ causally_open_future(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ tarentin(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- causally_arc_connected(C.dual) ⇏ causally_open_future(C) (refuted: Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- causally_arc_connected(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- causally_plain(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ causally_compact(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ push_up(C.dual) (refuted: Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ causally_open(C.dual) (refuted: Causal.notchedCausality_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ causally_open_future(C.dual) (refuted: Causal.notchedCausality_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- causally_plain(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.deux_pushup)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ tarentin(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.notchedCausality_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.notchedCausality_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- causally_plain(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- causally_plain(C.dual) ⇏ causally_open_future(C) (refuted: Causal.notchedCausality_separates_hasChronalNeighbour, time-reversed)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- causally_plain(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.notchedCausality_separates_hasChronalNeighbour, time-reversed)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- tarentin(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ causally_open(C.dual) (refuted: Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ causally_open_future(C.dual) (refuted: Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.globalLine_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- tarentin(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.globalLine_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.oneWayMembrane_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_not_chronalNeighbours)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.lightlikeLine_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- tarentin(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- tarentin(C.dual) ⇏ causally_open_future(C) (refuted: Causal.oneWayMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- tarentin(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.oneWayMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- time_function(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.jumpLine_separates_causallyOpenFuture)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- time_function(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ causally_plain(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- time_function(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- time_function(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- time_function(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- curves_extend(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileo_not_stronglyCausal)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ push_up(C.dual) (refuted: Causal.deux_pushup)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- curves_extend(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.gateLine_cauchyInclusion_not_causallyConvex)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- curves_extend(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- curves_extend(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- curves_extend(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ causally_plain(C.dual) (refuted: Causal.deux_pushup)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- locally_push_up(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- locally_push_up(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- locally_push_up(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ causally_open(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ causally_open_future(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ tarentin(C.dual) (refuted: Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.halfLightLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ is_causal(C) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ strongly_causal(C) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ strongly_causal_open(C) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ globally_hyperbolic(C) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ causally_compact(C) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ push_up(C) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ causally_open(C) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ causally_open_future(C) (refuted: Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ absolutely_minimal(C) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ causally_arc_connected(C) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ causally_plain(C) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ tarentin(C) (refuted: Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ time_function(C) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ locally_push_up(C) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ locally_causally_open(C) (refuted: Causal.halfLightLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ chronal_neighbours(C) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ has_chronal_neighbour(C) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ future_one_connected(C) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- locally_causally_open_future(C.dual) ⇏ locally_strongly_causal(C) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ causally_open(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ causally_open_future(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ causally_plain(C.dual) (refuted: Causal.lightlikeLine_not_causallyPlain)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ tarentin(C.dual) (refuted: Causal.spacelikeLine_separates_tarentin_full)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.lightlikeLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- locally_causally_open(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- locally_causally_open(C.dual) ⇏ causally_open_future(C) (refuted: Causal.gateLine_separates_causallyOpen, time-reversed)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ push_up(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ causally_open(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ causally_open_future(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.densCausality_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalJumpPlane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ causally_plain(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ locally_push_up(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- chronal_neighbours(C.dual) ⇏ causally_open_future(C) (refuted: Causal.chronalMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- chronal_neighbours(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.chronalMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ push_up(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ causally_open(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ causally_open_future(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.globalLine_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.globalLine_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ causally_plain(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ tarentin(C.dual) (refuted: Causal.notchedCausality_separates_hasChronalNeighbour)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ locally_push_up(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.chronalMembrane_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.closedHalfLine_separates_chronalNeighbours)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- has_chronal_neighbour(C.dual) ⇏ causally_open_future(C) (refuted: Causal.chronalMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- has_chronal_neighbour(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.chronalMembrane_separates, time-reversed)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ is_causal(C.dual) (refuted: Causal.symmRationalLine_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ causally_compact(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ push_up(C.dual) (refuted: Causal.halfChronoLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates_futureOneConnected, time-reversed)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.jumpLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ causally_plain(C.dual) (refuted: Causal.rationalLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ tarentin(C.dual) (refuted: Causal.loopFan_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ time_function(C.dual) (refuted: Causal.symmRationalLine_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates_futureOneConnected, time-reversed)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.loopFan_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.lightlikeLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- future_one_connected(C) ⇏ locally_strongly_causal(C.dual) (refuted: Causal.galileoCurve_separates)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- future_one_connected(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- future_one_connected(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates_futureOneConnected)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ is_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ strongly_causal(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ strongly_causal_open(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ globally_hyperbolic(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ causally_compact(C.dual) (refuted: Causal.halfPlane_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ push_up(C.dual) (refuted: Causal.gateLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ absolutely_minimal(C.dual) (refuted: Causal.gateLine_separates_causallyOpen)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ causally_arc_connected(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ causally_plain(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ tarentin(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ time_function(C.dual) (refuted: Causal.Flat.timeCylinder_separates_locallyStronglyCausal)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ locally_push_up(C.dual) (refuted: Causal.halfChronoLine_separates_pushUp)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ locally_causally_open_future(C.dual) (refuted: Causal.rationalLine_separates, time-reversed)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ locally_causally_open(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ chronal_neighbours(C.dual) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ has_chronal_neighbour(C.dual) (refuted: Causal.isolatedLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C) ⇏ future_one_connected(C.dual) (refuted: Causal.Flat.spaceCylinder_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- locally_strongly_causal(C.dual) ⇏ causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- locally_strongly_causal(C.dual) ⇏ locally_causally_open_future(C) (refuted: Causal.rationalLine_separates)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial

end
