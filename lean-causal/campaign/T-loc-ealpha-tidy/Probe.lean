import Causal.InextensiblePiece
import Causal.Model.StaticCauchy
import Causal.Model.EAlphaCauchy
import Causal.Model.HalfPlaneLadder

/-! Probe for T-loc-ealpha-tidy (not part of any library): `#check` and `#print axioms` on every
moved or new declaration, the module of each constant that moved, and the absence of the two
deleted duplicates. Run with `lake env lean campaign/T-loc-ealpha-tidy/Probe.lean` from
`lean-causal/`; the output is `axioms.txt`. -/

open Lean Meta

#check @Causal.Causality.inextensible_Iio_of_tendsto_not_mem
#check @Causal.staticCausality.Iminus_inter_slice
#check @Causal.staticCausality.IsRayTo
#check @Causal.staticCausality.IsRayTo.causalCurveIn
#check @Causal.staticCausality.IsRayTo.continuous
#check @Causal.staticCausality.IsRayTo.inextensible
#check @Causal.staticCausality.IsRayTo.infall
#check @Causal.staticCausality.IsRayTo.not_exists_isCauchySurfaceOn
#check @Causal.staticCausality.IsRayTo.not_globallyHyperbolicOn
#check @Causal.staticCausality.IsRayTo.not_isCauchySurfaceOn_of_subset_slice
#check @Causal.staticCausality.Jminus_diff_Iminus_inter_slice
#check @Causal.staticCausality.Jminus_eq_off_union
#check @Causal.staticCausality.Jminus_inter_slice
#check @Causal.staticCausality.Jplus_inter_slice
#check @Causal.staticCausality.causallyOpen
#check @Causal.staticCausality.chronalNeighbours
#check @Causal.staticCausality.hasTimeFunction
#check @Causal.staticCausality.isCauchySurface_slice
#check @Causal.staticCausality.isCauchyTimeFunction_sub_const
#check @Causal.staticCausality.isCompact_Jminus_inter_slice
#check @Causal.staticCausality.mem_offOpens
#check @Causal.staticCausality.noCausalEndpoint
#check @Causal.staticCausality.offOpens
#check @Causal.staticCausality.rayCurve
#check @Causal.staticCausality.stronglyCausalOpen
#check @Causal.halfPlane_separates
#check @Causal.properSpace_withLpTwo

#print axioms Causal.Causality.inextensible_Iio_of_tendsto_not_mem
#print axioms Causal.staticCausality.Iminus_inter_slice
#print axioms Causal.staticCausality.IsRayTo
#print axioms Causal.staticCausality.IsRayTo.causalCurveIn
#print axioms Causal.staticCausality.IsRayTo.continuous
#print axioms Causal.staticCausality.IsRayTo.inextensible
#print axioms Causal.staticCausality.IsRayTo.infall
#print axioms Causal.staticCausality.IsRayTo.not_exists_isCauchySurfaceOn
#print axioms Causal.staticCausality.IsRayTo.not_globallyHyperbolicOn
#print axioms Causal.staticCausality.IsRayTo.not_isCauchySurfaceOn_of_subset_slice
#print axioms Causal.staticCausality.Jminus_diff_Iminus_inter_slice
#print axioms Causal.staticCausality.Jminus_eq_off_union
#print axioms Causal.staticCausality.Jminus_inter_slice
#print axioms Causal.staticCausality.Jplus_inter_slice
#print axioms Causal.staticCausality.causallyOpen
#print axioms Causal.staticCausality.chronalNeighbours
#print axioms Causal.staticCausality.hasTimeFunction
#print axioms Causal.staticCausality.isCauchySurface_slice
#print axioms Causal.staticCausality.isCauchyTimeFunction_sub_const
#print axioms Causal.staticCausality.isCompact_Jminus_inter_slice
#print axioms Causal.staticCausality.mem_offOpens
#print axioms Causal.staticCausality.noCausalEndpoint
#print axioms Causal.staticCausality.offOpens
#print axioms Causal.staticCausality.rayCurve
#print axioms Causal.staticCausality.stronglyCausalOpen
#print axioms Causal.halfPlane_separates
#print axioms Causal.properSpace_withLpTwo

/- Every constant that moved (auxiliary ones included), the new theorem and the instance whose
proof term changed: its module and its axioms. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let names : List Name := [
    `Causal.Causality.inextensible_Iio_of_tendsto_not_mem,
    `Causal.Causality.inextensible_Iio_of_tendsto_not_mem._simp_1_1,
    `Causal.Causality.inextensible_Iio_of_tendsto_not_mem._simp_1_2,
    `Causal.Causality.inextensible_Iio_of_tendsto_not_mem._simp_1_3,
    `Causal.staticCausality.Iminus_inter_slice,
    `Causal.staticCausality.Iminus_inter_slice._simp_1_1,
    `Causal.staticCausality.Iminus_inter_slice._simp_1_2,
    `Causal.staticCausality.Iminus_inter_slice._simp_1_3,
    `Causal.staticCausality.Iminus_inter_slice._simp_1_4,
    `Causal.staticCausality.Iminus_inter_slice._simp_1_5,
    `Causal.staticCausality.IsRayTo,
    `Causal.staticCausality.IsRayTo.casesOn,
    `Causal.staticCausality.IsRayTo.causalCurveIn,
    `Causal.staticCausality.IsRayTo.continuous,
    `Causal.staticCausality.IsRayTo.inextensible,
    `Causal.staticCausality.IsRayTo.infall,
    `Causal.staticCausality.IsRayTo.lip,
    `Causal.staticCausality.IsRayTo.mem_zero,
    `Causal.staticCausality.IsRayTo.mk,
    `Causal.staticCausality.IsRayTo.mk._flat_ctor,
    `Causal.staticCausality.IsRayTo.not_exists_isCauchySurfaceOn,
    `Causal.staticCausality.IsRayTo.not_globallyHyperbolicOn,
    `Causal.staticCausality.IsRayTo.not_isCauchySurfaceOn_of_subset_slice,
    `Causal.staticCausality.IsRayTo.not_mem,
    `Causal.staticCausality.IsRayTo.rec,
    `Causal.staticCausality.IsRayTo.recOn,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice._simp_1_1,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice._simp_1_2,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice._simp_1_3,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice._simp_1_4,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice._simp_1_5,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice._simp_1_6,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice._simp_1_7,
    `Causal.staticCausality.Jminus_diff_Iminus_inter_slice._simp_1_8,
    `Causal.staticCausality.Jminus_eq_off_union,
    `Causal.staticCausality.Jminus_eq_off_union._simp_1_1,
    `Causal.staticCausality.Jminus_eq_off_union._simp_1_2,
    `Causal.staticCausality.Jminus_eq_off_union._simp_1_3,
    `Causal.staticCausality.Jminus_eq_off_union._simp_1_4,
    `Causal.staticCausality.Jminus_eq_off_union._simp_1_5,
    `Causal.staticCausality.Jminus_inter_slice,
    `Causal.staticCausality.Jminus_inter_slice._simp_1_1,
    `Causal.staticCausality.Jminus_inter_slice._simp_1_2,
    `Causal.staticCausality.Jminus_inter_slice._simp_1_3,
    `Causal.staticCausality.Jminus_inter_slice._simp_1_4,
    `Causal.staticCausality.Jminus_inter_slice._simp_1_5,
    `Causal.staticCausality.Jplus_inter_slice,
    `Causal.staticCausality.Jplus_inter_slice._simp_1_1,
    `Causal.staticCausality.Jplus_inter_slice._simp_1_2,
    `Causal.staticCausality.Jplus_inter_slice._simp_1_3,
    `Causal.staticCausality.Jplus_inter_slice._simp_1_4,
    `Causal.staticCausality.Jplus_inter_slice._simp_1_5,
    `Causal.staticCausality.causallyOpen,
    `Causal.staticCausality.chronalNeighbours,
    `Causal.staticCausality.hasTimeFunction,
    `Causal.staticCausality.isCauchySurface_slice,
    `Causal.staticCausality.isCauchySurface_slice._simp_1_1,
    `Causal.staticCausality.isCauchyTimeFunction_sub_const,
    `Causal.staticCausality.isCompact_Jminus_inter_slice,
    `Causal.staticCausality.mem_offOpens,
    `Causal.staticCausality.noCausalEndpoint,
    `Causal.staticCausality.offOpens,
    `Causal.staticCausality.offOpens._proof_1,
    `Causal.staticCausality.offOpens.congr_simp,
    `Causal.staticCausality.rayCurve,
    `Causal.staticCausality.rayCurve.eq_1,
    `Causal.staticCausality.stronglyCausalOpen,
    `Causal.halfPlane_separates,
    `Causal.properSpace_withLpTwo]
  for n in names do
    let some idx := env.getModuleIdxFor? n | throwError "{n} not found"
    let ax ← collectAxioms n
    IO.println s!"{n}\t{env.header.moduleNames[idx.toNat]!}\t{ax.toList}"
  IO.println s!"{names.length} constants"
  for n in [`Causal.withLp_dist_fst_le, `Causal.withLp_dist_snd_le] do
    IO.println s!"{n} in the environment: {env.contains n}"
