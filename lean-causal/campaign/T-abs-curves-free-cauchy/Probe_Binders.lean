import Lean
import Causal.CExtConnexeSecondCountable
import Causal.ErsSecondCountable
import Causal.CauchySeparation
import CausalScaffold.CurvesFreeCauchy.CompactCauchy
import CausalScaffold.CurvesFreeCauchy.CausalConvex
import CausalScaffold.CurvesFreeCauchy.Basic
open Lean Meta Elab Command

/-- `#binders n` logs one JSON line: the binder list (info, name, type) and the conclusion. -/
elab "#binders " n:ident : command => do
  let some ci := (← getEnv).find? n.getId | throwError "unknown {n.getId}"
  let s ← liftTermElabM <| forallTelescope ci.type fun xs body => do
    let mut arr : Array Json := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      let bi := match d.binderInfo with
        | .default => "()" | .implicit => "{}" | .strictImplicit => "⦃⦄" | .instImplicit => "[]"
      let nm := if d.binderInfo == .instImplicit then "_inst" else d.userName.eraseMacroScopes.toString
      let ty := toString (← ppExpr d.type)
      arr := arr.push (Json.arr #[Json.str bi, Json.str nm, Json.str ty])
    let concl := toString (← ppExpr body)
    return (Json.mkObj [("name", Json.str n.getId.toString), ("binders", Json.arr arr),
      ("concl", Json.str concl)]).compress
  logInfo m!"BINDERS {s}"

#binders Causal.Causality.eq_of_le_of_isCauchySurfaceOn
#binders Causal.Causality.eq_of_le_of_isCauchySurfaceOn_secondCountable
#binders Causal.Causality.mem_Jplus_or_Jminus_of_isCauchySurfaceOn
#binders Causal.Causality.mem_Jplus_or_Jminus_of_isCauchySurfaceOn_secondCountable
#binders Causal.Causality.exists_box_of_twoSided
#binders Causal.Causality.exists_box_of_twoSided_secondCountable
#binders Causal.Causality.exists_graph
#binders Causal.Causality.exists_graph_secondCountable
#binders Causal.Causality.exists_sign_nhds
#binders Causal.Causality.exists_sign_nhds_secondCountable
#binders Causal.Causality.isAcausal_of_graph
#binders Causal.Causality.isAcausal_of_graph_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_secondCountable
#binders Causal.Causality.inter_subsingleton_of_curvesExtend
#binders Causal.Causality.inter_subsingleton_of_t1_secondCountable
#binders Causal.Causality.isCauchySurfaceOn_iff_of_curvesExtend
#binders Causal.Causality.isCauchySurfaceOn_iff_of_t1_secondCountable
#binders Causal.Causality.exists_inextensible_inf_meeting_of_subsingleton
#binders Causal.Causality.exists_inextensible_inf_meeting_of_subsingleton_secondCountable
#binders Causal.Causality.exists_inextensible_inf_meeting
#binders Causal.Causality.exists_inextensible_inf_meeting_secondCountable
#binders Causal.Causality.mem_connectedComponentIn_inf_of_subsingleton
#binders Causal.Causality.mem_connectedComponentIn_inf_of_subsingleton_secondCountable
#binders Causal.Causality.mem_connectedComponentIn_inf
#binders Causal.Causality.mem_connectedComponentIn_inf_secondCountable
#binders Causal.Causality.isPreconnected_inf_of_subset
#binders Causal.Causality.isPreconnected_inf_of_subset_secondCountable
#binders Causal.Causality.isPreconnected_inf
#binders Causal.Causality.isPreconnected_inf_secondCountable
#binders Causal.IsCauchyEmbedding.c_ext_connexe_of_isCauchySurfaceOn
#binders Causal.IsCauchyEmbedding.c_ext_connexe_of_isCauchySurfaceOn_secondCountable
#binders Causal.Causality.image_Icc_subset_of_curvesExtend
#binders Causal.Causality.image_Icc_subset_of_secondCountable
#binders Causal.Causality.CurvesExtend.dual
#binders Causal.Causality.CurvesExtend.dual_secondCountable
#binders Causal.IsCausalIso.curvesExtend
#binders Causal.IsCausalIso.curvesExtend_secondCountable
#binders Causal.Causality.IsCauchySurfaceOn.eq_of_le
#binders Causal.Causality.IsCauchySurfaceOn.eq_of_le_of_t1_secondCountable
#binders Causal.Causality.IsCauchySurface.isAcausal
#binders Causal.Causality.IsCauchySurface.isAcausal_of_t1_secondCountable
#binders Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface
#binders Causal.Causality.IsCauchySurface.cover_of_t1_secondCountable
#binders Causal.Causality.Jplus_mem_nhds_of_isCauchySurface
#binders Causal.Causality.Jplus_mem_nhds_of_isCauchySurface_of_secondCountable
#binders Causal.Causality.Jminus_mem_nhds_of_isCauchySurface
#binders Causal.Causality.Jminus_mem_nhds_of_isCauchySurface_of_secondCountable
#binders Causal.IsCauchyEmbedding.image_diamant
#binders Causal.IsCauchyEmbedding.image_diamant_of_secondCountable
#binders Causal.IsCauchyEmbedding.diamond_subset_range
#binders Causal.IsCauchyEmbedding.diamond_subset_range_of_secondCountable
#binders Causal.IsCauchyEmbedding.passe_pgcd
#binders Causal.IsCauchyEmbedding.passe_pgcd_of_secondCountable
#binders Causal.IsCauchyEmbedding.passe_pgcd_explicit
#binders Causal.IsCauchyEmbedding.passe_pgcd_explicit_of_secondCountable
#binders Causal.IsCauchyEmbedding.eq_of_mem_image_inter
#binders Causal.IsCauchyEmbedding.eq_of_mem_image_inter_of_secondCountable
#binders Causal.IsCauchyEmbedding.exists_inextensible_inf
#binders Causal.IsCauchyEmbedding.exists_inextensible_inf_of_secondCountable
#binders Causal.IsCauchyEmbedding.isPreconnected_inf
#binders Causal.IsCauchyEmbedding.isPreconnected_inf_of_secondCountable
#binders Causal.IsCauchyEmbedding.c_ext_connexe_of_isConnected
#binders Causal.IsCauchyEmbedding.c_ext_connexe_of_isConnected_of_secondCountable
#binders Causal.IsCauchyEmbedding.c_ext_connexe'
#binders Causal.IsCauchyEmbedding.c_ext_connexe'_of_secondCountable
#binders Causal.IsCauchyEmbedding.isPreconnected_inf_of_preconnectedSpace
#binders Causal.IsCauchyEmbedding.isPreconnected_inf_of_preconnectedSpace_of_secondCountable
#binders Causal.IsCauchyEmbedding.c_ext_connexe_of_connectedSpace
#binders Causal.IsCauchyEmbedding.c_ext_connexe_of_connectedSpace_of_secondCountable
#binders Causal.IsCauchyEmbedding.isCauchySurfaceOn_inf_iff
#binders Causal.IsCauchyEmbedding.isCauchySurfaceOn_inf_iff_of_secondCountable
#binders Causal.IsCauchyEmbedding.inf_causallyConvexIn
#binders Causal.IsCauchyEmbedding.inf_causallyConvexIn_of_secondCountable
#binders Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn
#binders Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn_of_secondCountable
#binders Causal.IsCauchyInclusion.causallyConvexIn
#binders Causal.IsCauchyInclusion.causallyConvexIn_of_secondCountable
#binders Causal.Causality.isCauchySurfaceOn_iSup
#binders Causal.Causality.isCauchySurfaceOn_iSup_of_secondCountable
#binders Causal.isCauchyInclusion_iSup_of_common
#binders Causal.isCauchyInclusion_iSup_of_common_of_secondCountable
#binders Causal.isCauchyInclusion_iSup
#binders Causal.isCauchyInclusion_iSup_of_secondCountable
#binders Causal.isCauchyInclusion_sSup
#binders Causal.isCauchyInclusion_sSup_of_secondCountable
#binders Causal.Causality.ers_lemma_4_72
#binders Causal.Causality.ers_lemma_4_72_secondCountable
#binders Causal.Causality.ers_lemma_4_72_isConnected
#binders Causal.Causality.ers_lemma_4_72_isConnected_secondCountable

#print axioms Causal.Causality.eq_of_le_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.Causality.mem_Jplus_or_Jminus_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.Causality.exists_box_of_twoSided_secondCountable
#print axioms Causal.Causality.exists_graph_secondCountable
#print axioms Causal.Causality.exists_sign_nhds_secondCountable
#print axioms Causal.Causality.isAcausal_of_graph_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_secondCountable
#print axioms Causal.timelikeLine_isCauchySurface_zero_of_lemmaK_secondCountable
#print axioms Causal.timelikeLine_isCauchySurface_one_of_lemmaK_secondCountable
#print axioms Causal.Causality.inter_subsingleton_of_t1_secondCountable
#print axioms Causal.Causality.isCauchySurfaceOn_iff_of_t1_secondCountable
#print axioms Causal.Causality.exists_inextensible_inf_meeting_of_subsingleton_secondCountable
#print axioms Causal.Causality.exists_inextensible_inf_meeting_secondCountable
#print axioms Causal.Causality.mem_connectedComponentIn_inf_of_subsingleton_secondCountable
#print axioms Causal.Causality.mem_connectedComponentIn_inf_secondCountable
#print axioms Causal.Causality.isPreconnected_inf_of_subset_secondCountable
#print axioms Causal.Causality.isPreconnected_inf_secondCountable
#print axioms Causal.IsCauchyEmbedding.c_ext_connexe_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.timelikeLine_isPreconnected_inf_secondCountable
#print axioms Causal.timelikeLine_c_ext_connexe_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.timelikeLine_gateArc_c_ext_connexe_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.Causality.image_Icc_subset_of_secondCountable
#print axioms Causal.Causality.CurvesExtend.dual_secondCountable
#print axioms Causal.IsCausalIso.curvesExtend_secondCountable
#print axioms Causal.timelikeLine_image_Icc_subset_secondCountable
#print axioms Causal.timelikeLine_dual_curvesExtend_secondCountable
#print axioms Causal.timelikeLine_transport_curvesExtend_secondCountable
