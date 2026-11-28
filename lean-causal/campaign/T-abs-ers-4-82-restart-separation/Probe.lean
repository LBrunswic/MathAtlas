import CausalScaffold.Ers482RestartSeparation

/-! Probe of T-abs-ers-4-82-restart-separation: the type and the axioms of every declaration of
`CausalScaffold.Ers482RestartSeparation`, and a check that the last conjunct of
`restart_separation` negates exactly the `hrestart` binder of both uniform forms. -/

#check @Causal.spacelikeLine_subset_of_isCauchySurfaceOn
#check @Causal.Ers482Separation.mark
#check @Causal.Ers482Separation.cauSep
#check @Causal.Ers482Separation.dom₀
#check @Causal.Ers482Separation.dom₂
#check @Causal.Ers482Separation.glue₀₂
#check @Causal.Ers482Separation.mem_dom₀
#check @Causal.Ers482Separation.mem_dom₂
#check @Causal.Ers482Separation.mark_of_mem
#check @Causal.Ers482Separation.mark_of_notMem
#check @Causal.Ers482Separation.cauSep_id
#check @Causal.Ers482Separation.cauSep_mark
#check @Causal.Ers482Separation.cauSep_of_not
#check @Causal.Ers482Separation.cauSep_eq_of_isDevelopment
#check @Causal.Ers482Separation.glue₀₂_of_mem
#check @Causal.Ers482Separation.glue₀₂_of_notMem
#check @Causal.Ers482Separation.cauSep_glue₀₂
#check @Causal.Ers482Separation.isDevelopment_ersWitnessIoo_sep
#check @Causal.Ers482Separation.isMaximalDevelopment_ersWitnessIoo_sep
#check @Causal.Ers482Separation.isDevelopment_dom₀
#check @Causal.Ers482Separation.isDevelopment_dom₂
#check @Causal.Ers482Separation.hG_sep
#check @Causal.Ers482Separation.hT_sep
#check @Causal.Ers482Separation.hconn_sep
#check @Causal.Ers482Separation.component₀₂
#check @Causal.Ers482Separation.frontier_component₀₂
#check @Causal.Ers482Separation.not_gluedRestartAt_pair
#check @Causal.Ers482Separation.restart_separation
#check @Causal.Ers482Separation.restart_separation_forms
#check @Causal.Ers482Separation.hstep_solution
#check @Causal.Ers482Separation.cauSep_ers_theorem_4_82_solution
#check @Causal.Ers482Separation.not_causalityFollows_cauSep

open Causal Causal.Ers482Separation in
/-- `hr` is typed once, by the domain of the two uniform forms applied to the first sixteen
conjuncts, and the same `hr` is fed to the negated last conjunct: the three domains agree. -/
example : True := by
  obtain ⟨hloc, hglue, hres, hs₀, hmax, honesided, hconn, hG, hT, hcaus, hsplit, hJm, hJp, hK,
    hSclosed, hagree, -, hn⟩ := restart_separation
  have _h : ∀ hr, ers_theorem_4_82_solution_of_restarts hloc hglue hres hs₀ hmax honesided hconn
      hG hT hsplit hK hSclosed hagree hr = ers_theorem_4_82_solution_of_restarts_isCausal hloc
      hglue hres hs₀ hmax honesided hconn hcaus hsplit hJm hJp hK hSclosed hagree hr → False :=
    fun hr _ => hn hr
  trivial

#print axioms Causal.spacelikeLine_subset_of_isCauchySurfaceOn
#print axioms Causal.Ers482Separation.mark
#print axioms Causal.Ers482Separation.cauSep
#print axioms Causal.Ers482Separation.dom₀
#print axioms Causal.Ers482Separation.dom₂
#print axioms Causal.Ers482Separation.glue₀₂
#print axioms Causal.Ers482Separation.mem_dom₀
#print axioms Causal.Ers482Separation.mem_dom₂
#print axioms Causal.Ers482Separation.mark_of_mem
#print axioms Causal.Ers482Separation.mark_of_notMem
#print axioms Causal.Ers482Separation.cauSep_id
#print axioms Causal.Ers482Separation.cauSep_mark
#print axioms Causal.Ers482Separation.cauSep_of_not
#print axioms Causal.Ers482Separation.cauSep_eq_of_isDevelopment
#print axioms Causal.Ers482Separation.glue₀₂_of_mem
#print axioms Causal.Ers482Separation.glue₀₂_of_notMem
#print axioms Causal.Ers482Separation.cauSep_glue₀₂
#print axioms Causal.Ers482Separation.isDevelopment_ersWitnessIoo_sep
#print axioms Causal.Ers482Separation.isMaximalDevelopment_ersWitnessIoo_sep
#print axioms Causal.Ers482Separation.isDevelopment_dom₀
#print axioms Causal.Ers482Separation.isDevelopment_dom₂
#print axioms Causal.Ers482Separation.hG_sep
#print axioms Causal.Ers482Separation.hT_sep
#print axioms Causal.Ers482Separation.hconn_sep
#print axioms Causal.Ers482Separation.component₀₂
#print axioms Causal.Ers482Separation.frontier_component₀₂
#print axioms Causal.Ers482Separation.not_gluedRestartAt_pair
#print axioms Causal.Ers482Separation.restart_separation
#print axioms Causal.Ers482Separation.restart_separation_forms
#print axioms Causal.Ers482Separation.hstep_solution
#print axioms Causal.Ers482Separation.cauSep_ers_theorem_4_82_solution
#print axioms Causal.Ers482Separation.not_causalityFollows_cauSep
