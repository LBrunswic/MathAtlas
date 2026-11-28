import CausalScaffold.FlrwTypeClosedAmbient
-- The model is imported by this probe only, to check the layer-3 re-derivations; the
-- module itself imports Causal.FlrwType alone (layer 1).
import Causal.Model.MinkowskiPastBoundaryChart

set_option pp.proofs false

#check @Causal.Causality.isClosed_inter_preimage_setOf_le
#check @Causal.Causality.IsCauchySurfaceOn.mem_Jplus_union_Jminus
#check @Causal.Causality.PastBoundaryChartData.false_of_squeeze
#check @Causal.Causality.not_pastBoundaryChart_of_flrwTypeA_of_closedIn
#check @Causal.Causality.not_pastBoundaryChart_of_flrwTypeA_of_isClosed_le
#check @Causal.Causality.GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeA
#check @Causal.Causality.GloballyHyperbolic.not_flrwTypeA_of_pastBoundaryChart
#check @Causal.Causality.dual_iUnion_Iplus_eq_of_futureInextensible
#check @Causal.Causality.not_futureBoundaryChart_of_flrwTypeA_of_closedIn
#check @Causal.Causality.not_futureBoundaryChart_of_flrwTypeA_of_isClosed_le
#check @Causal.Causality.GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeA
#check @Causal.Causality.not_pastBoundaryChart_of_flrwTypeB_of_closedIn
#check @Causal.Causality.not_pastBoundaryChart_of_flrwTypeB_of_isClosed_le
#check @Causal.Causality.GloballyHyperbolic.not_pastBoundaryChart_of_flrwTypeB
#check @Causal.Causality.GloballyHyperbolic.not_flrwTypeB_of_pastBoundaryChart
#check @Causal.Causality.not_futureBoundaryChart_of_flrwTypeB_of_isClosed_le
#check @Causal.Causality.not_futureBoundaryChart_of_flrwTypeB_of_closedIn
#check @Causal.timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeA
#check @Causal.timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeB

#print axioms Causal.Causality.isClosed_inter_preimage_setOf_le
#print axioms Causal.Causality.IsCauchySurfaceOn.mem_Jplus_union_Jminus
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
#print axioms Causal.Causality.not_futureBoundaryChart_of_flrwTypeB_of_isClosed_le
#print axioms Causal.Causality.not_futureBoundaryChart_of_flrwTypeB_of_closedIn
#print axioms Causal.timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeA
#print axioms Causal.timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeB

namespace Causal

/-- The instance check at the Minkowski half-space: (A) fails, re-derived from the chart by
`GloballyHyperbolic.not_flrwTypeA_of_pastBoundaryChart` (closedness and antisymmetry), not by
`minkowski_posHalfSpace_not_flrwTypeA`'s explicit point. -/
theorem probe_minkowski_posHalfSpace_not_flrwTypeA {n : ℕ} (hn : 0 < n) :
    ¬ ∀ (I : Set ℝ) (γ : ℝ → Minkowski n),
      (minkowski n).PastInextensible (minkowskiPosHalfSpace n) I γ →
      (∀ a ∈ I, ∀ b ∈ I, (minkowski n).ChronalCurveOn (minkowskiPosHalfSpace n) γ a b) →
      ⋃ t ∈ I, (minkowski n).Iplus (minkowskiPosHalfSpace n) {γ t} = minkowskiPosHalfSpace n :=
  Causality.GloballyHyperbolic.not_flrwTypeA_of_pastBoundaryChart minkowski_tarentin
    minkowski_globallyHyperbolic (minkowski_pastBoundaryChart hn)

/-- The same for (B), by `GloballyHyperbolic.not_flrwTypeB_of_pastBoundaryChart`; the half-space
is causally arc-connected by `minkowski_posHalfSpace_flrwType_check`. -/
theorem probe_minkowski_posHalfSpace_not_flrwTypeB {n : ℕ} (hn : 0 < n) :
    ¬ ∀ x ∈ minkowskiPosHalfSpace n, ∃ S : Set (Minkowski n),
      (minkowski n).IsCauchySurfaceOn (minkowskiPosHalfSpace n) S ∧
        S ⊆ (minkowski n).Iminus (minkowskiPosHalfSpace n) {x} :=
  Causality.GloballyHyperbolic.not_flrwTypeB_of_pastBoundaryChart minkowski_tarentin
    minkowski_globallyHyperbolic (minkowski_posHalfSpace_flrwType_check hn).2.2.2.1
    (minkowski_pastBoundaryChart hn)

/-- The corollary on every open set of `𝐌^{1+n}`: (A) excludes a past boundary chart. -/
theorem probe_minkowski_not_pastBoundaryChart_of_flrwTypeA {n : ℕ}
    (W : TopologicalSpace.Opens (Minkowski n))
    (hA : ∀ (I : Set ℝ) (γ : ℝ → Minkowski n), (minkowski n).PastInextensible W I γ →
      (∀ a ∈ I, ∀ b ∈ I, (minkowski n).ChronalCurveOn W γ a b) →
      ⋃ t ∈ I, (minkowski n).Iplus W {γ t} = W)
    (Ũ : TopologicalSpace.Opens (Minkowski n)) (p : Minkowski n) :
    ¬ (minkowski n).PastBoundaryChart W Ũ p :=
  minkowski_globallyHyperbolic.not_pastBoundaryChart_of_flrwTypeA minkowski_tarentin hA Ũ p

end Causal

#print axioms Causal.probe_minkowski_posHalfSpace_not_flrwTypeA
#print axioms Causal.probe_minkowski_posHalfSpace_not_flrwTypeB
#print axioms Causal.probe_minkowski_not_pastBoundaryChart_of_flrwTypeA
