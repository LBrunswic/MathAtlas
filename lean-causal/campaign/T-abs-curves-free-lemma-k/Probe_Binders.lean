import Lean
import Causal.LemmaK
import Causal.LemmaKObstruction
import Causal.LevinUtility
import CausalScaffold.CurvesFreeLemmaK.Local
open Lean Meta Elab Command

/-! kb/0227's pair check for T-abs-curves-free-lemma-k. Run from lean-causal/ (after building the
four CausalScaffold.CurvesFreeLemmaK modules):
    lake env lean campaign/T-abs-curves-free-lemma-k/Probe_Binders.lean > /tmp/binders.out 2>&1
    python3 -I campaign/T-abs-curves-free-lemma-k/binders_diff.py /tmp/binders.out \
        campaign/T-abs-curves-free-lemma-k/binders_pairs.json campaign/T-abs-curves-free-lemma-k/binders_diff.json
-/

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

#binders Causal.Causality.exists_lt_of_le_of_isCauchySurfaceOn
#binders Causal.Causality.exists_lt_of_le_of_isCauchySurfaceOn_secondCountable
#binders Causal.Causality.exists_lt_of_le_of_ne_of_isLocallyCauchy
#binders Causal.Causality.exists_lt_of_le_of_ne_of_isLocallyCauchy_secondCountable
#binders Causal.Causality.isOpen_strictJplus_of_Zminus
#binders Causal.Causality.isOpen_strictJplus_of_Zminus_secondCountable
#binders Causal.Causality.isOpen_strictJplus_of_twoSided
#binders Causal.Causality.isOpen_strictJplus_of_twoSided_secondCountable
#binders Causal.Causality.isAcausal_of_isLocallyCauchy
#binders Causal.Causality.isAcausal_of_isLocallyCauchy_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_chronal
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_chronal_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp_secondCountable
#binders Causal.Causality.isOpen_strictJplus_of_isCauchySplitting
#binders Causal.Causality.isOpen_strictJplus_of_isCauchySplitting_secondCountable
#binders Causal.Causality.isCauchySurface_of_isCauchySplitting_via_strictJplus
#binders Causal.Causality.isCauchySurface_of_isCauchySplitting_via_strictJplus_secondCountable
#binders Causal.Causality.isCauchySurface_iff_of_curvesExtend
#binders Causal.Causality.isCauchySurface_iff_of_secondCountable
#binders Causal.Causality.isOpen_strictJplus_of_isCauchySurface
#binders Causal.Causality.isOpen_strictJplus_of_isCauchySurface_secondCountable
#binders Causal.Causality.isAcausal_of_isLocallyCauchy_of_relOpen
#binders Causal.Causality.isAcausal_of_isLocallyCauchy_of_relOpen_secondCountable
#binders Causal.Causality.isAcausal_iff_of_isLocallyCauchy
#binders Causal.Causality.isAcausal_iff_of_isLocallyCauchy_secondCountable
#binders Causal.Causality.isCauchySurface_iff_local
#binders Causal.Causality.isCauchySurface_iff_local_of_secondCountable
#binders Causal.Causality.isCauchySurface_iff_isOpen_strictJplus
#binders Causal.Causality.isCauchySurface_iff_isOpen_strictJplus_of_secondCountable
#binders Causal.Causality.exists_nhds_subset_Jplus_of_isCauchySurfaceOn
#binders Causal.Causality.exists_nhds_subset_Jplus_of_isCauchySurfaceOn_secondCountable
#binders Causal.Causality.isOpen_Jplus_diff_of_isCauchySurfaceOn
#binders Causal.Causality.isOpen_Jplus_diff_of_isCauchySurfaceOn_secondCountable
#binders Causal.Causality.isOpen_Jminus_diff_of_isCauchySurfaceOn
#binders Causal.Causality.isOpen_Jminus_diff_of_isCauchySurfaceOn_secondCountable
#binders Causal.Causality.isLocallyCauchyTwoSided_iff
#binders Causal.Causality.isLocallyCauchyTwoSided_iff_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_splitting
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_splitting_secondCountable
#binders Causal.Causality.isOpen_chartFutureSide
#binders Causal.Causality.isOpen_chartFutureSide_secondCountable
#binders Causal.Causality.strictJplus_eq_Jplus_chartFutureSide
#binders Causal.Causality.strictJplus_eq_Jplus_chartFutureSide_secondCountable
#binders Causal.Causality.isCauchySurface_of_isOpen_Jplus_chartFutureSide
#binders Causal.Causality.isCauchySurface_of_isOpen_Jplus_chartFutureSide_secondCountable
#binders Causal.Causality.IsLocallyCauchy.isLocallyCauchyTwoSided
#binders Causal.Causality.isLocallyCauchyTwoSided_of_secondCountable
#binders Causal.Causality.isCauchySurface_iff_isOpen_Jplus_chartFutureSide
#binders Causal.Causality.isCauchySurface_iff_isOpen_Jplus_chartFutureSide_of_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable
#binders Causal.Causality.local_conditions_of_isOpen_Jplus
#binders Causal.Causality.local_conditions_of_isOpen_Jplus_of_secondCountable
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen_of_curvesExtend
#binders Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen

#print axioms Causal.Causality.exists_lt_of_le_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.Causality.exists_lt_of_le_of_ne_of_isLocallyCauchy_secondCountable
#print axioms Causal.Causality.isOpen_strictJplus_of_Zminus_secondCountable
#print axioms Causal.Causality.isOpen_strictJplus_of_twoSided_secondCountable
#print axioms Causal.Causality.isAcausal_of_isLocallyCauchy_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_chronal_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp_secondCountable
#print axioms Causal.Causality.isOpen_strictJplus_of_isCauchySplitting_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isCauchySplitting_via_strictJplus_secondCountable
#print axioms Causal.Causality.isCauchySurface_iff_of_secondCountable
#print axioms Causal.Causality.isOpen_strictJplus_of_isCauchySurface_secondCountable
#print axioms Causal.Causality.isAcausal_of_isLocallyCauchy_of_relOpen_secondCountable
#print axioms Causal.Causality.isAcausal_iff_of_isLocallyCauchy_secondCountable
#print axioms Causal.Causality.isCauchySurface_iff_local_of_secondCountable
#print axioms Causal.Causality.isCauchySurface_iff_isOpen_strictJplus_of_secondCountable
#print axioms Causal.Causality.exists_nhds_subset_Jplus_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.Causality.isOpen_Jplus_diff_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.Causality.isOpen_Jminus_diff_of_isCauchySurfaceOn_secondCountable
#print axioms Causal.Causality.isLocallyCauchyTwoSided_iff_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_splitting_secondCountable
#print axioms Causal.Causality.isOpen_chartFutureSide_secondCountable
#print axioms Causal.Causality.strictJplus_eq_Jplus_chartFutureSide_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isOpen_Jplus_chartFutureSide_secondCountable
#print axioms Causal.Causality.isLocallyCauchyTwoSided_of_secondCountable
#print axioms Causal.Causality.isCauchySurface_iff_isOpen_Jplus_chartFutureSide_of_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable
#print axioms Causal.Causality.local_conditions_of_isOpen_Jplus_of_secondCountable
#print axioms Causal.Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen
#print axioms Causal.timelikeLine_isCauchySurface_zero_of_lemmaKBare_secondCountable
#print axioms Causal.timelikeLine_isCauchySurface_zero_of_lemmaKBare_twoSided_secondCountable
#print axioms Causal.timelikeLine_isCauchySurface_zero_of_lemmaKBare_gx_secondCountable
#print axioms Causal.timelikeLine_reduction_hypotheses_secondCountable
#print axioms Causal.timelikeLine_isCauchySurface_zero_of_reduction_secondCountable
#print axioms Causal.timelikeLine_isOpen_strictJplus_zero_secondCountable
#print axioms Causal.timelikeLine_lemmaKSC_local_secondCountable
#print axioms Causal.timelikeLine_isAcausal_zero_of_relOpen_secondCountable
#print axioms Causal.timelikeLine_isAcausal_zero_iff_secondCountable
#print axioms Causal.timelikeLine_isCauchySurface_zero_of_lemmaKLocal_pushUp_secondCountable
#print axioms Causal.timelikeLine_isCauchySurface_zero_of_lemmaKLocal_splitting_secondCountable
#print axioms Causal.timelikeLine_isLocallyCauchyTwoSided_zero_secondCountable
#print axioms Causal.timelikeLine_strictJplus_zero_eq_secondCountable
#print axioms Causal.timelikeLine_isCauchySurface_zero_of_chartFutureSide_secondCountable
