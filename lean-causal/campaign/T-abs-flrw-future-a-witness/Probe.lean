import Causal.FlrwTypeClosedAmbient
import Causal.LineDevelopment
import Causal.TimelikeHomotopy

/-! Probe for T-abs-flrw-future-a-witness (scratch; not a library module). It imports the edited
module `Causal.FlrwTypeClosedAmbient` and, for the non-vacuity examples only, two ETT-layer modules
that the edited module does not import: `Causal.LineDevelopment`
(`futureInextensible_of_not_tendsto_atTop`) and `Causal.TimelikeHomotopy`
(`timelikeLine_chronalCurveOn_iff`). It checks the three new declarations, shows that their
hypotheses are discharged on a concrete instance and are not vacuous, and prints the axioms of
the three new declarations and of every existing declaration of the module. Its output is
`axioms.txt`. -/

set_option pp.proofs false

-- The three new declarations
#check @Causal.Causality.iUnion_Iminus_eq_of_dual_pastInextensible
#check @Causal.timelikeLine_posHalfLine_iUnion_Iminus_eq
#check @Causal.timelikeLine_posHalfLine_not_futureBoundaryChart_of_flrwTypeA

namespace Causal
open Set Filter Topology Causality

/-! ### (a) and its twin are the two directions of one equivalence -/

example {M : Type*} [TopologicalSpace M] (C : Causality M) (W : TopologicalSpace.Opens M) :
    (∀ (I : Set ℝ) (γ : ℝ → M), C.FutureInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.Iminus W {γ t} = W) ↔
    (∀ (I : Set ℝ) (γ : ℝ → M), C.dual.PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, C.dual.ChronalCurveOn W γ a b) → ⋃ t ∈ I, C.dual.Iplus W {γ t} = W) :=
  ⟨dual_iUnion_Iplus_eq_of_futureInextensible, iUnion_Iminus_eq_of_dual_pastInextensible⟩

/-! ### (a) is used with a hypothesis that holds: (A) for the reversed line on `(0, ∞)` -/

-- the hypothesis `hA` of `iUnion_Iminus_eq_of_dual_pastInextensible` at `C = timelikeLine`,
-- `W = posHalfLine`, the one the proof of (b) feeds it, is a theorem here
theorem probe_dual_posHalfLine_iUnion_Iplus_eq :
    ∀ (J : Set ℝ) (δ : ℝ → ℝ), timelikeLine.dual.PastInextensible posHalfLine J δ →
      (∀ a ∈ J, ∀ b ∈ J, timelikeLine.dual.ChronalCurveOn posHalfLine δ a b) →
      ⋃ t ∈ J, timelikeLine.dual.Iplus posHalfLine {δ t} = posHalfLine :=
  dual_iUnion_Iplus_eq_of_futureInextensible timelikeLine_posHalfLine_iUnion_Iminus_eq

/-! ### The hypotheses are not vacuous: a future-inextensible chronal curve of `(0, ∞)` -/

-- `exp` over `ℝ` is a chronal curve of `(0, ∞)` on every segment
theorem probe_exp_chronal (a b : ℝ) : timelikeLine.ChronalCurveOn posHalfLine Real.exp a b :=
  timelikeLine_chronalCurveOn_iff.2 ⟨Real.exp_strictMono.strictMonoOn _,
    Real.continuous_exp.continuousOn, fun t _ => Real.exp_pos t⟩

-- and it is future-inextensible in `(0, ∞)`: it has no limit there at `+∞`
theorem probe_exp_futureInextensible :
    timelikeLine.FutureInextensible posHalfLine univ Real.exp :=
  LineDevelopment.futureInextensible_of_not_tendsto_atTop
    ⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ => (probe_exp_chronal a b).causalCurveOn⟩
    (fun x _ h => not_tendsto_nhds_of_tendsto_atTop Real.tendsto_exp_atTop x h)

-- so (b) has a concrete instance: `⋃ t, I⁻(exp t, (0, ∞)) = (0, ∞)`
example : ⋃ t ∈ (univ : Set ℝ), timelikeLine.Iminus posHalfLine {Real.exp t} = posHalfLine :=
  timelikeLine_posHalfLine_iUnion_Iminus_eq univ Real.exp probe_exp_futureInextensible
    (fun a _ b _ => probe_exp_chronal a b)

-- and (a)'s hypothesis has a concrete instance: `t ↦ exp (-t)` is a past-inextensible chronal
-- curve of `(0, ∞)` for the reversed line
example : timelikeLine.dual.PastInextensible posHalfLine univ (fun t => Real.exp (-t)) := by
  have h := (dual_pastInextensible_iff (C := timelikeLine) (W := posHalfLine) (I := univ)
    (c := Real.exp)).2 probe_exp_futureInextensible
  rwa [neg_univ] at h

example : ⋃ t ∈ (univ : Set ℝ), timelikeLine.dual.Iplus posHalfLine {Real.exp (-t)} =
    posHalfLine := by
  have h := (dual_pastInextensible_iff (C := timelikeLine) (W := posHalfLine) (I := univ)
    (c := Real.exp)).2 probe_exp_futureInextensible
  rw [neg_univ] at h
  exact probe_dual_posHalfLine_iUnion_Iplus_eq univ _ h
    (fun a _ b _ => CurveOn.neg (probe_exp_chronal (-b) (-a)))

/-! ### (c)'s hypotheses, discharged on the timelike line -/

example : T2Space ℝ := inferInstance
example : timelikeLine.Tarentin := timelikeLine_tarentin
example : timelikeLine.GloballyHyperbolic := timelikeLine_globallyHyperbolic

-- (c) is the theorem applied, not `timelikeLine_not_futureBoundaryChart`
example (Ũ : TopologicalSpace.Opens ℝ) (p : ℝ) :
    ¬ timelikeLine.FutureBoundaryChart posHalfLine Ũ p :=
  timelikeLine_globallyHyperbolic.not_futureBoundaryChart_of_flrwTypeA (W := posHalfLine)
    timelikeLine_tarentin timelikeLine_posHalfLine_iUnion_Iminus_eq Ũ p

end Causal

-- Axioms: the three new declarations
#print axioms Causal.Causality.iUnion_Iminus_eq_of_dual_pastInextensible
#print axioms Causal.timelikeLine_posHalfLine_iUnion_Iminus_eq
#print axioms Causal.timelikeLine_posHalfLine_not_futureBoundaryChart_of_flrwTypeA

-- Axioms: the probe's non-vacuity lemmas
#print axioms Causal.probe_dual_posHalfLine_iUnion_Iplus_eq
#print axioms Causal.probe_exp_chronal
#print axioms Causal.probe_exp_futureInextensible

-- Axioms: every existing declaration of Causal.FlrwTypeClosedAmbient
#print axioms Causal.Causality.isClosed_inter_preimage_setOf_le
#print axioms Causal.Causality.PastBoundaryChartData.false_of_squeeze
#print axioms Causal.Causality.not_pastBoundaryChart_of_flrwTypeA_of_closedIn
#print axioms Causal.Causality.not_pastBoundaryChart_of_flrwTypeA_of_isClosed_le
#print axioms Causal.Causality.GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeA
#print axioms Causal.Causality.GloballyHyperbolic.not_flrwTypeA_of_pastBoundaryChart
#print axioms Causal.Causality.dual_iUnion_Iplus_eq_of_futureInextensible
#print axioms Causal.Causality.not_futureBoundaryChart_of_flrwTypeA_of_closedIn
#print axioms Causal.Causality.not_futureBoundaryChart_of_flrwTypeA_of_isClosed_le
#print axioms Causal.Causality.GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeA
#print axioms Causal.Causality.not_pastBoundaryChart_of_flrwTypeB_of_closedIn
#print axioms Causal.Causality.not_pastBoundaryChart_of_flrwTypeB_of_isClosed_le
#print axioms Causal.Causality.GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeB
#print axioms Causal.Causality.GloballyHyperbolic.not_flrwTypeB_of_pastBoundaryChart
#print axioms Causal.Causality.not_futureBoundaryChart_of_flrwTypeB_of_closedIn
#print axioms Causal.Causality.not_futureBoundaryChart_of_flrwTypeB_of_isClosed_le
#print axioms Causal.Causality.GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeB
#print axioms Causal.timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeA
#print axioms Causal.timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeB
#print axioms Causal.timelikeLine_posHalfLine_not_futureBoundaryChart_of_flrwTypeB
