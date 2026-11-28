import Causal.FlrwTypeClosedAmbient

/-! Probe for T-abs-flrw-future-extension. It imports `Causal.FlrwTypeClosedAmbient`, which imports
`Causal.FlrwType`: the two edited modules. It checks the seven new declarations, two definitional
facts the time reversal rests on, and the axioms of every declaration of both modules. Its output is
`axioms.txt`. -/

set_option pp.proofs false

-- The seven new declarations
#check @Causal.IsSpacetimeExtension.not_futureBoundaryChart_of_flrwType
#check @Causal.timelikeLine_not_futureBoundaryChart
#check @Causal.timelikeLine_iUnion_Iminus_eq_univ
#check @Causal.timelikeLine_exists_cauchy_Iplus
#check @Causal.timelikeLine_exp_not_futureBoundaryChart
#check @Causal.Causality.GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeB
#check @Causal.timelikeLine_posHalfLine_not_futureBoundaryChart_of_flrwTypeB

namespace Causal
open Causality

-- `hι.dual.rangeOpens` is `hι.rangeOpens` by `rfl`: both are `⟨range ι, _⟩`
example {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N] [Nonempty N]
    {CN : Causality N} {C : Causality M} {ι : N → M} (hι : IsSpacetimeExtension CN C ι) :
    hι.dual.rangeOpens = hι.rangeOpens := rfl

-- `FutureBoundaryChart` is the past boundary chart of `C.dual`, by `rfl`
example {M : Type*} [TopologicalSpace M] (C : Causality M) (W Ũ : TopologicalSpace.Opens M)
    (p : M) : C.FutureBoundaryChart W Ũ p = C.dual.PastBoundaryChart W Ũ p := rfl

end Causal

-- Axioms: the seven new declarations
#print axioms Causal.IsSpacetimeExtension.not_futureBoundaryChart_of_flrwType
#print axioms Causal.timelikeLine_not_futureBoundaryChart
#print axioms Causal.timelikeLine_iUnion_Iminus_eq_univ
#print axioms Causal.timelikeLine_exists_cauchy_Iplus
#print axioms Causal.timelikeLine_exp_not_futureBoundaryChart
#print axioms Causal.Causality.GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeB
#print axioms Causal.timelikeLine_posHalfLine_not_futureBoundaryChart_of_flrwTypeB

-- Axioms: every existing declaration of Causal.FlrwType and Causal.FlrwTypeClosedAmbient
#print axioms Causal.Causality.PastBoundaryChartData
#print axioms Causal.Causality.PastBoundaryChart
#print axioms Causal.Causality.FutureBoundaryChart
#print axioms Causal.Causality.ChronalCurveOn.pastInextensible_Ioc_of_start_notMem
#print axioms Causal.Causality.PastBoundaryChartData.Iplus_inter_Iminus_subset
#print axioms Causal.Causality.PastBoundaryChartData.biUnion_Iplus_inter_Iminus_eq
#print axioms Causal.Causality.PastBoundaryChartData.Iminus_eq_diamond
#print axioms Causal.Causality.PastBoundaryChartData.subset_diamond
#print axioms Causal.Causality.not_pastBoundaryChart_of_flrwType
#print axioms Causal.Causality.not_futureBoundaryChart_of_flrwType
#print axioms Causal.IsSpacetimeExtension.isCauchySurfaceOn_image
#print axioms Causal.IsSpacetimeExtension.le_antisymm_rangeOpens
#print axioms Causal.IsSpacetimeExtension.iUnion_Iplus_eq_of_pastInextensible
#print axioms Causal.IsSpacetimeExtension.exists_isCauchySurfaceOn_subset_Iminus
#print axioms Causal.IsSpacetimeExtension.not_pastBoundaryChart_of_flrwType
#print axioms Causal.posHalfLine
#print axioms Causal.timelikeLine_not_pastBoundaryChart
#print axioms Causal.timelikeLine_iUnion_Iplus_eq_univ
#print axioms Causal.timelikeLine_exists_cauchy_Iminus
#print axioms Causal.exp_rangeOpens_eq
#print axioms Causal.timelikeLine_exp_not_pastBoundaryChart
#print axioms Causal.timelikeLine_flrwType_hypotheses_posHalfLine
#print axioms Causal.timelikeLine_posHalfLine_not_pastBoundaryChart
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
#print axioms Causal.timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeA
#print axioms Causal.timelikeLine_posHalfLine_not_pastBoundaryChart_of_flrwTypeB
