import CausalScaffold.MeetsCauchyAntisymmetrySharp

set_option pp.proofs false

#check @Causal.Causality.CausalCurveIn.continuousOn_interval
#check @Causal.Causality.causalCurveIn_top_of_pieces
#check @Causal.Causality.extensible_of_graph_of_bddAbove
#check @Causal.Causality.extensible_of_graph
#check @Causal.rayCircleSet
#check @Causal.RayCircleArc
#check @Causal.rayCircleArc
#check @Causal.rayCircleArc_mem
#check @Causal.rayCircleγ
#check @Causal.rayCircle
#check @Causal.rayCircleQ
#check @Causal.rayCircleY
#check @Causal.continuous_rayCircleγ
#check @Causal.rayCircle_causallyArcConnected
#check @Causal.rayCircle_absolutelyMinimal
#check @Causal.rayCircle_absolutelyMinimalOn
#check @Causal.rayCircleQ_ne_Y
#check @Causal.rayCircleγ_up_zero
#check @Causal.rayCircleγ_up_one
#check @Causal.rayCircleγ_low_zero
#check @Causal.rayCircleγ_low_one
#check @Causal.rayCircle_le_Q_Y
#check @Causal.rayCircle_le_Y_Q
#check @Causal.rayCircle_not_isCausal
#check @Causal.rayCircleC
#check @Causal.rayCircleC_re
#check @Causal.rayCircleC_im
#check @Causal.continuous_rayCircleC
#check @Causal.rayCircle_arg_cos_add_sin
#check @Causal.rayCircleAngle
#check @Causal.rayCircleAngle_up
#check @Causal.rayCircleAngle_low
#check @Causal.rayCircleAngle_ray
#check @Causal.rayCircleAngle_le_of_arcStep
#check @Causal.rayCircleAngle_le_of_le
#check @Causal.continuousOn_rayCircleAngle
#check @Causal.rayCircleAngle_le_pi
#check @Causal.rayCirclePathRay
#check @Causal.rayCirclePathRay_mem
#check @Causal.rayCircleCurveRay
#check @Causal.rayCircleCurveLow
#check @Causal.rayCircleCurveRay_pi
#check @Causal.rayCircleCurveLow_pi
#check @Causal.continuous_rayCircleCurveRay
#check @Causal.continuous_rayCircleCurveLow
#check @Causal.rayCircleγ_ray_eq
#check @Causal.rayCircleγ_up_eq_ray
#check @Causal.rayCircleγ_up_eq_low
#check @Causal.rayCircleγ_low_eq_low
#check @Causal.rayCircle_le_curveRay_of_nonpos
#check @Causal.rayCircle_le_curveRay_of_nonneg
#check @Causal.rayCircle_le_curveLow_of_nonpos
#check @Causal.rayCircle_le_curveLow_of_nonneg
#check @Causal.rayCircleCurveRay_causalCurveIn
#check @Causal.rayCircleCurveLow_causalCurveIn
#check @Causal.rayCircle_circle_of_le_one
#check @Causal.rayCircle_le_one_of_circle
#check @Causal.rayCircleC_norm_of_circle
#check @Causal.rayCircleAngle_of_circle
#check @Causal.rayCircleCurveLow_arg
#check @Causal.rayCircleCurveRay_angle
#check @Causal.rayCircleCurveLow_angle
#check @Causal.rayCircle_extensible_of_forall_ne
#check @Causal.rayCircle_isCauchySurface_Y
#check @Causal.rayCircleRay
#check @Causal.rayCircleRay_fst
#check @Causal.rayCircleRay_causalCurveIn
#check @Causal.rayCircleRay_pastInextensible
#check @Causal.rayCircleRay_zero
#check @Causal.rayCircleRay_zero_mem_Jplus
#check @Causal.rayCircleRay_ne_Y
#check @Causal.rayCircle_separates_pastInextensible_meets
#check @Causal.not_pastInextensible_exists_mem_of_mem_Jplus_bare

#print axioms Causal.Causality.CausalCurveIn.continuousOn_interval
#print axioms Causal.Causality.causalCurveIn_top_of_pieces
#print axioms Causal.Causality.extensible_of_graph_of_bddAbove
#print axioms Causal.Causality.extensible_of_graph
#print axioms Causal.rayCircleSet
#print axioms Causal.RayCircleArc
#print axioms Causal.rayCircleArc
#print axioms Causal.rayCircleArc_mem
#print axioms Causal.rayCircleγ
#print axioms Causal.rayCircle
#print axioms Causal.rayCircleQ
#print axioms Causal.rayCircleY
#print axioms Causal.continuous_rayCircleγ
#print axioms Causal.rayCircle_causallyArcConnected
#print axioms Causal.rayCircle_absolutelyMinimal
#print axioms Causal.rayCircle_absolutelyMinimalOn
#print axioms Causal.rayCircleQ_ne_Y
#print axioms Causal.rayCircleγ_up_zero
#print axioms Causal.rayCircleγ_up_one
#print axioms Causal.rayCircleγ_low_zero
#print axioms Causal.rayCircleγ_low_one
#print axioms Causal.rayCircle_le_Q_Y
#print axioms Causal.rayCircle_le_Y_Q
#print axioms Causal.rayCircle_not_isCausal
#print axioms Causal.rayCircleC
#print axioms Causal.rayCircleC_re
#print axioms Causal.rayCircleC_im
#print axioms Causal.continuous_rayCircleC
#print axioms Causal.rayCircle_arg_cos_add_sin
#print axioms Causal.rayCircleAngle
#print axioms Causal.rayCircleAngle_up
#print axioms Causal.rayCircleAngle_low
#print axioms Causal.rayCircleAngle_ray
#print axioms Causal.rayCircleAngle_le_of_arcStep
#print axioms Causal.rayCircleAngle_le_of_le
#print axioms Causal.continuousOn_rayCircleAngle
#print axioms Causal.rayCircleAngle_le_pi
#print axioms Causal.rayCirclePathRay
#print axioms Causal.rayCirclePathRay_mem
#print axioms Causal.rayCircleCurveRay
#print axioms Causal.rayCircleCurveLow
#print axioms Causal.rayCircleCurveRay_pi
#print axioms Causal.rayCircleCurveLow_pi
#print axioms Causal.continuous_rayCircleCurveRay
#print axioms Causal.continuous_rayCircleCurveLow
#print axioms Causal.rayCircleγ_ray_eq
#print axioms Causal.rayCircleγ_up_eq_ray
#print axioms Causal.rayCircleγ_up_eq_low
#print axioms Causal.rayCircleγ_low_eq_low
#print axioms Causal.rayCircle_le_curveRay_of_nonpos
#print axioms Causal.rayCircle_le_curveRay_of_nonneg
#print axioms Causal.rayCircle_le_curveLow_of_nonpos
#print axioms Causal.rayCircle_le_curveLow_of_nonneg
#print axioms Causal.rayCircleCurveRay_causalCurveIn
#print axioms Causal.rayCircleCurveLow_causalCurveIn
#print axioms Causal.rayCircle_circle_of_le_one
#print axioms Causal.rayCircle_le_one_of_circle
#print axioms Causal.rayCircleC_norm_of_circle
#print axioms Causal.rayCircleAngle_of_circle
#print axioms Causal.rayCircleCurveLow_arg
#print axioms Causal.rayCircleCurveRay_angle
#print axioms Causal.rayCircleCurveLow_angle
#print axioms Causal.rayCircle_extensible_of_forall_ne
#print axioms Causal.rayCircle_isCauchySurface_Y
#print axioms Causal.rayCircleRay
#print axioms Causal.rayCircleRay_fst
#print axioms Causal.rayCircleRay_causalCurveIn
#print axioms Causal.rayCircleRay_pastInextensible
#print axioms Causal.rayCircleRay_zero
#print axioms Causal.rayCircleRay_zero_mem_Jplus
#print axioms Causal.rayCircleRay_ne_Y
#print axioms Causal.rayCircle_separates_pastInextensible_meets
#print axioms Causal.not_pastInextensible_exists_mem_of_mem_Jplus_bare
