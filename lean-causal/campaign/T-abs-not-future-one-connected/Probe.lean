import CausalScaffold.Model.FlatSpaceCylinder

/-! Probe for T-abs-not-future-one-connected: the main declarations, their axioms, and the
projections the keeper's [[fails]] entry reads. Run with
`taskset -c 0-11 lake env lean -DwarningAsError=true campaign/T-abs-not-future-one-connected/Probe.lean`
after `lake build CausalScaffold.Model.FlatSpaceCylinder`. -/

open Causal Causal.Flat TopologicalSpace

#check @Causal.Flat.spaceCylinder_separates
#check @Causal.Flat.spaceCylinder_not_futureOneConnected
#check @Causal.Flat.windCurve_not_chronallyHomotopicOn
#check @Causal.Flat.windCurve_chronalCurveOn
#check @Causal.Flat.spaceCylinder_globallyHyperbolic
#check @Causal.Flat.finite_le_spaceGroup
#check @Causal.Causality.ChronalHomotopyOn.homotopicRel
#check @Causal.IsEMorphismOn.chronalCurveOn_comp

#print axioms Causal.Flat.spaceCylinder_separates
#print axioms Causal.Flat.spaceCylinder_not_futureOneConnected
#print axioms Causal.Flat.windCurve_not_chronallyHomotopicOn
#print axioms Causal.Flat.windCurve_chronalCurveOn
#print axioms Causal.Flat.spaceCylinder_globallyHyperbolic
#print axioms Causal.Flat.finite_le_spaceGroup
#print axioms Causal.Flat.spaceCylinder_pushUp
#print axioms Causal.Flat.spaceCylinder_causallyOpen
#print axioms Causal.Flat.spaceCylinder_absolutelyMinimal
#print axioms Causal.Flat.spaceCylinder_absolutelyMinimalOn
#print axioms Causal.Flat.spaceCylinder_causallyArcConnected
#print axioms Causal.Flat.spaceCylinder_causallyPlain
#print axioms Causal.Flat.spaceCylinder_chronalNeighbours
#print axioms Causal.Flat.spaceCylinder_tarentin
#print axioms Causal.Flat.spaceCylinder_curvesExtend
#print axioms Causal.Flat.spaceCylinder_hasTimeFunction
#print axioms Causal.Causality.ChronalHomotopyOn.homotopicRel
#print axioms Causal.IsEMorphismOn.chronalCurveOn_comp
#print axioms Causal.Flat.isLocalIsometry_mk_top
#print axioms Causal.Flat.isEMorphism_spaceCylinderMk

/-- The dispatch's form: the topology, the seven provided nodes and ¬ FutureOneConnected. -/
example :
    (T2Space SpaceCylinder ∧ SecondCountableTopology SpaceCylinder ∧
      ConnectedSpace SpaceCylinder) ∧
    spaceCylinder.GloballyHyperbolic ∧ spaceCylinder.PushUp ∧ spaceCylinder.CausallyOpen ∧
    spaceCylinder.AbsolutelyMinimal ∧ spaceCylinder.CausallyArcConnected ∧
    spaceCylinder.CausallyPlain ∧ spaceCylinder.ChronalNeighbours ∧
    ¬ spaceCylinder.FutureOneConnected := by
  obtain ⟨ht, h1, h2, h3, h4, h5, h6, h7, -, -, -, -, -, -, -, -, -, -, -, -, -, hn⟩ :=
    spaceCylinder_separates
  exact ⟨ht, h1, h2, h3, h4, h5, h6, h7, hn⟩

/-- Each of the 19 [[open]] entries' `from`, with the negated `to`, projected from the one
witness (the nodes in the ladder's order of the [[open]] block, programme/ladder.toml:4869–4962). -/
example :
    (spaceCylinder.AbsolutelyMinimal ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.CausallyArcConnected ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.CausallyCompact ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.CausallyOpen ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.CausallyOpenFuture ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.CausallyPlain ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.ChronalNeighbours ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.CurvesExtend ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.GloballyHyperbolic ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.HasChronalNeighbourEverywhere ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.IsCausal ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.LocallyCausallyOpen ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.LocallyCausallyOpenFuture ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.LocallyPushUp ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.PushUp ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.StronglyCausal ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.StronglyCausalOpen ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.Tarentin ∧ ¬ spaceCylinder.FutureOneConnected) ∧
    (spaceCylinder.HasTimeFunction ∧ ¬ spaceCylinder.FutureOneConnected) := by
  obtain ⟨-, gh, pu, co, am, cac, cp, cn, cc, cof, ce, hcn, ic, lco, lcof, lpu, sc, sco, ta, tf, -,
    hn⟩ := spaceCylinder_separates
  exact ⟨⟨am, hn⟩, ⟨cac, hn⟩, ⟨cc, hn⟩, ⟨co, hn⟩, ⟨cof, hn⟩, ⟨cp, hn⟩, ⟨cn, hn⟩, ⟨ce, hn⟩, ⟨gh, hn⟩,
    ⟨hcn, hn⟩, ⟨ic, hn⟩, ⟨lco, hn⟩, ⟨lcof, hn⟩, ⟨lpu, hn⟩, ⟨pu, hn⟩, ⟨sc, hn⟩, ⟨sco, hn⟩,
    ⟨ta, hn⟩, ⟨tf, hn⟩⟩

/-- The abstract theorems apply without restatement: the time-reversed cylinder is not future
one-connected either (`Causality.dual_futureOneConnected`, an iff of the ETT layer). -/
example : ¬ spaceCylinder.dual.FutureOneConnected := fun h =>
  spaceCylinder_not_futureOneConnected (Causality.dual_futureOneConnected.1 h)

/-- Five pairwise non-homotopic chronal curves from `[(0, 0)]` to `[(3, 0)]`, for every open set:
the winding numbers `-2, …, 2`. -/
example (W : Opens SpaceCylinder) :
    ¬ spaceCylinder.ChronallyHomotopicOn W (windCurve ((-2 : ℤ) : ℝ)) (windCurve ((2 : ℤ) : ℝ)) :=
  windCurve_not_chronallyHomotopicOn (by norm_num) W

/-- The evidence's two curves are future chronal curves (`|k| < 3`). -/
example : spaceCylinder.ChronalCurveOn ⊤ (windCurve 0) 0 1 ∧
    spaceCylinder.ChronalCurveOn ⊤ (windCurve 1) 0 1 :=
  ⟨windCurve_chronalCurveOn (by norm_num), windCurve_chronalCurveOn (by norm_num)⟩
