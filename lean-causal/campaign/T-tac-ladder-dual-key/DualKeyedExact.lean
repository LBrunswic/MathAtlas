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

-- causally_open_future introduces causally_open: Causal.Causality.causallyOpen_iff (an iff)
theorem causallyOpen_of_future_of_past (hf : Causal.Causality.CausallyOpenFuture C) (hp : Causal.Causality.CausallyOpenFuture C.dual) : Causal.Causality.CausallyOpen C :=
  Causal.Causality.causallyOpen_iff.2 ⟨hf, hp⟩
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

-- curve_nested: Causal.Causality.dual_curveNestedOn_iff (an iff)
theorem curveNestedOn_of_dual (h : Causal.Causality.CurveNestedOn C.dual C'.dual W) : Causal.Causality.CurveNestedOn C C' W :=
  Causal.Causality.dual_curveNestedOn_iff.1 h
theorem curveNestedOn_dual (h : Causal.Causality.CurveNestedOn C C' W) : Causal.Causality.CurveNestedOn C.dual C'.dual W :=
  Causal.Causality.dual_curveNestedOn_iff.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] curveNestedOn_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] curveNestedOn_dual

-- inextensible_nested: Causal.Causality.dual_inextensibleNestedOn_iff (an iff)
theorem inextensibleNestedOn_of_dual (h : Causal.Causality.InextensibleNestedOn C.dual C'.dual W) : Causal.Causality.InextensibleNestedOn C C' W :=
  Causal.Causality.dual_inextensibleNestedOn_iff.1 h
theorem inextensibleNestedOn_dual (h : Causal.Causality.InextensibleNestedOn C C' W) : Causal.Causality.InextensibleNestedOn C.dual C'.dual W :=
  Causal.Causality.dual_inextensibleNestedOn_iff.2 h
attribute [aesop safe forward (rule_sets := [CausalLadder])] inextensibleNestedOn_of_dual
attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] inextensibleNestedOn_dual

end Causal.LadderDual

section
universe u
variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M)

example (_h0 : Causal.Causality.IsCausal C) : Causal.Causality.IsCausal C.dual := by causal_ladder
example (_h0 : Causal.Causality.IsCausal C.dual) : Causal.Causality.IsCausal C := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausal C) : Causal.Causality.StronglyCausal C.dual := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausal C) : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausal C.dual) : Causal.Causality.StronglyCausal C := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausal C.dual) : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.StronglyCausal C.dual := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausalOpen C) : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.StronglyCausal C := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.StronglyCausalOpen C := by causal_ladder
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.IsCausal C.dual := by causal_ladder
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
example (_h0 : Causal.Causality.GloballyHyperbolic C) : Causal.Causality.CausallyCompact C.dual := by causal_ladder
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.IsCausal C := by causal_ladder
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.GloballyHyperbolic C := by causal_ladder
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : Causal.Causality.CausallyCompact C := by causal_ladder
example (_h0 : Causal.Causality.CausallyCompact C) : Causal.Causality.CausallyCompact C.dual := by causal_ladder
example (_h0 : Causal.Causality.CausallyCompact C.dual) : Causal.Causality.CausallyCompact C := by causal_ladder
example (_h0 : Causal.Causality.PushUp C) : Causal.Causality.PushUp C.dual := by causal_ladder
example (_h0 : Causal.Causality.PushUp C) : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
example (_h0 : Causal.Causality.PushUp C.dual) : Causal.Causality.PushUp C := by causal_ladder
example (_h0 : Causal.Causality.PushUp C.dual) : Causal.Causality.LocallyPushUp C := by causal_ladder
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.CausallyOpen C.dual := by causal_ladder
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
example (_h0 : Causal.Causality.CausallyOpen C) : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.CausallyOpen C := by causal_ladder
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.CausallyOpenFuture C := by causal_ladder
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
example (_h0 : Causal.Causality.CausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
example (_h0 : Causal.Causality.CausallyArcConnected C) : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
example (_h0 : Causal.Causality.CausallyArcConnected C) : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : Causal.Causality.CausallyArcConnected C := by causal_ladder
example (_h0 : Causal.Causality.CausallyPlain C) : Causal.Causality.CausallyPlain C.dual := by causal_ladder
example (_h0 : Causal.Causality.CausallyPlain C.dual) : Causal.Causality.CausallyPlain C := by causal_ladder
example (_h0 : Causal.Causality.Tarentin C) : Causal.Causality.Tarentin C.dual := by causal_ladder
example (_h0 : Causal.Causality.Tarentin C.dual) : Causal.Causality.Tarentin C := by causal_ladder
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.IsCausal C.dual := by causal_ladder
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
example (_h0 : Causal.Causality.HasTimeFunction C) : Causal.Causality.CurvesExtend C.dual := by causal_ladder
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.IsCausal C := by causal_ladder
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.HasTimeFunction C := by causal_ladder
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : Causal.Causality.CurvesExtend C := by causal_ladder
example (_h0 : Causal.Causality.CurvesExtend C) : Causal.Causality.CurvesExtend C.dual := by causal_ladder
example (_h0 : Causal.Causality.CurvesExtend C.dual) : Causal.Causality.CurvesExtend C := by causal_ladder
example (_h0 : Causal.Causality.LocallyPushUp C) : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : Causal.Causality.LocallyPushUp C := by causal_ladder
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
example (_h0 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.Tarentin C.dual := by causal_ladder
example (_h0 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
example (_h0 : Causal.Causality.ChronalNeighbours C) : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.Tarentin C := by causal_ladder
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.ChronalNeighbours C := by causal_ladder
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
example (_h0 : Causal.Causality.FutureOneConnected C) : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : Causal.Causality.FutureOneConnected C := by causal_ladder
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
-- refuted ('is_causal', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('is_causal', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('strongly_causal', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('strongly_causal_open', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('globally_hyperbolic', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('causally_compact', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('push_up', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('causally_open', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('causally_open_future', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('absolutely_minimal', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('causally_arc_connected', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('causally_plain', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('tarentin', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.HasTimeFunction C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('time_function', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.HasTimeFunction C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.CurvesExtend C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('curves_extend', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.CurvesExtend C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('locally_push_up', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('locally_causally_open_future', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('locally_causally_open', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('chronal_neighbours', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- refuted ('has_chronal_neighbour', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 0) ⇏ ('locally_strongly_causal', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('future_one_connected', 1) ⇏ ('locally_strongly_causal', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyStronglyCausal C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('strongly_causal', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('globally_hyperbolic', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('causally_compact', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('push_up', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.PushUp C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('causally_open', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('causally_open_future', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('absolutely_minimal', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('causally_arc_connected', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('causally_plain', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('tarentin', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.Tarentin C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('time_function', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('locally_causally_open_future', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('locally_causally_open', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('chronal_neighbours', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('has_chronal_neighbour', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 0) ⇏ ('future_one_connected', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C.dual := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('strongly_causal', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausal C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('globally_hyperbolic', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.GloballyHyperbolic C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('causally_compact', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyCompact C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('push_up', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.PushUp C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('causally_open', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpen C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('causally_open_future', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('absolutely_minimal', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Precausality.AbsolutelyMinimal C.toPrecausality := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('causally_arc_connected', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyArcConnected C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('causally_plain', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CausallyPlain C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('tarentin', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.Tarentin C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('time_function', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.HasTimeFunction C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('locally_causally_open_future', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpenFuture C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('locally_causally_open', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyCausallyOpen C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('chronal_neighbours', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.ChronalNeighbours C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('has_chronal_neighbour', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.HasChronalNeighbourEverywhere C := by causal_ladder
  trivial
-- refuted ('locally_strongly_causal', 1) ⇏ ('future_one_connected', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.FutureOneConnected C := by causal_ladder
  trivial
-- unknown ('is_causal', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.IsCausal C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('is_causal', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.IsCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('strongly_causal', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- unknown ('strongly_causal', 0) ⇏ ('strongly_causal_open', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C.dual := by causal_ladder
  trivial
-- unknown ('strongly_causal', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.StronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('strongly_causal', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- unknown ('strongly_causal', 1) ⇏ ('strongly_causal_open', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.StronglyCausalOpen C := by causal_ladder
  trivial
-- unknown ('strongly_causal', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.StronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('strongly_causal_open', 0) ⇏ ('is_causal', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.IsCausal C.dual := by causal_ladder
  trivial
-- unknown ('strongly_causal_open', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.StronglyCausalOpen C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('strongly_causal_open', 1) ⇏ ('is_causal', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.IsCausal C := by causal_ladder
  trivial
-- unknown ('strongly_causal_open', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.StronglyCausalOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('globally_hyperbolic', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.GloballyHyperbolic C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('globally_hyperbolic', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.GloballyHyperbolic C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('causally_compact', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.CausallyCompact C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('causally_compact', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.CausallyCompact C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('push_up', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.PushUp C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('push_up', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.PushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('causally_open', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.CausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('causally_open', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.CausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('causally_open_future', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.CausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('causally_open_future', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.CausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('absolutely_minimal', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('absolutely_minimal', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Precausality.AbsolutelyMinimal C.dual.toPrecausality) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('causally_arc_connected', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.CausallyArcConnected C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('causally_arc_connected', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.CausallyArcConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('causally_plain', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('causally_plain', 0) ⇏ ('locally_push_up', 1)
example (_h0 : Causal.Causality.CausallyPlain C) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C.dual := by causal_ladder
  trivial
-- unknown ('causally_plain', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('causally_plain', 1) ⇏ ('locally_push_up', 0)
example (_h0 : Causal.Causality.CausallyPlain C.dual) : True := by
  fail_if_success have : Causal.Causality.LocallyPushUp C := by causal_ladder
  trivial
-- unknown ('tarentin', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.Tarentin C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('tarentin', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.Tarentin C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('locally_push_up', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.LocallyPushUp C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('locally_push_up', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.LocallyPushUp C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('locally_causally_open_future', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('locally_causally_open_future', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpenFuture C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('locally_causally_open', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.LocallyCausallyOpen C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('locally_causally_open', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.LocallyCausallyOpen C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('chronal_neighbours', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.ChronalNeighbours C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('chronal_neighbours', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.ChronalNeighbours C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('has_chronal_neighbour', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('has_chronal_neighbour', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.HasChronalNeighbourEverywhere C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('future_one_connected', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.FutureOneConnected C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('future_one_connected', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.FutureOneConnected C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial
-- unknown ('locally_strongly_causal', 0) ⇏ ('curves_extend', 1)
example (_h0 : Causal.Causality.LocallyStronglyCausal C) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C.dual := by causal_ladder
  trivial
-- unknown ('locally_strongly_causal', 1) ⇏ ('curves_extend', 0)
example (_h0 : Causal.Causality.LocallyStronglyCausal C.dual) : True := by
  fail_if_success have : Causal.Causality.CurvesExtend C := by causal_ladder
  trivial

end
