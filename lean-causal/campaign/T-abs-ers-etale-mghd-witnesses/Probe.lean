import CausalScaffold.ErsEtaleMghdWitnesses

/-! Probe of T-abs-ers-etale-mghd-witnesses: the type and the axioms of every declaration of
`CausalScaffold.ErsEtaleMghdWitnesses`, and two checks by the kernel. (1) The finding
`ers_coe_eq_inter_of_eqOn` gives the conclusion of `ers_isOpenEmbedding_proj_of_eqOn` through the
hypothesis-free `EtaleGluing.injective_proj_iff`: the theorem's content is `A = U₁ ∩ U₂`. (2) At
the 4.68 witness of the line, `U₂` is a development of `{0}` for no causality, so
`real_eqOn_inter_of_isDevelopment` does not apply there, and the witness does not contradict it.
The probe is not a copy of the module; it imports it. -/

#check @Causal.ers_coe_eq_inter_of_eqOn
#check @Causal.real_eqOn_inter_of_isDevelopment
#check @Causal.timelikeLine_isCauchySurfaceOn_Ioo_of_mem
#check @Causal.timelikeLine_isCauchySurfaceOn_union_Ioo
#check @Causal.ErsEtaleWitness.lineA_subset_top
#check @Causal.ErsEtaleWitness.lineA_subset_disU₂
#check @Causal.ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale
#check @Causal.ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale_doubled
#check @Causal.ErsEtaleWitness.twoU₁
#check @Causal.ErsEtaleWitness.twoU₂
#check @Causal.ErsEtaleWitness.twoA
#check @Causal.ErsEtaleWitness.twoSol₂
#check @Causal.ErsEtaleWitness.twoA_subset₁
#check @Causal.ErsEtaleWitness.twoA_subset₂
#check @Causal.ErsEtaleWitness.eqOn_twoSol₂
#check @Causal.ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale_twoPoint
#check @Causal.ErsEtaleWitness.timelikeLine_ers_theorem_3_45_etale_twoPoint
#check @Causal.ErsEtaleWitness.timelikeLine_ers_isPreconnected_inter_of_eqOn
#check @Causal.ErsEtaleWitness.timelikeLine_ers_isOpenEmbedding_proj_of_eqOn

open Causal Causal.EtaleGluing in
/-- (1) The forced `A = U₁ ∩ U₂` gives injectivity with no further hypothesis, at the line. -/
example : Function.Injective (proj lineA_subset₁ lineA_subset₂) := by
  obtain ⟨-, -, -, hA⟩ := ErsEtaleWitness.timelikeLine_ers_isOpenEmbedding_proj_of_eqOn
  exact injective_proj_iff.2 hA.symm.subset

open Causal in
/-- (2) The 4.68 witness's `U₂` is a development of `{0}` for no problem. -/
example : ¬ ∃ (sol : TopologicalSpace.Opens ℝ → (ℝ → ℝ) → Prop) (cau : (ℝ → ℝ) → Causality ℝ),
    IsDevelopment sol cau {0} ErsWitness.disU₂ ErsWitness.disSol₂ := by
  rintro ⟨sol, cau, hd⟩
  exact (ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale_doubled).2.2.2.2 _ hd.cauchy

#print axioms Causal.ers_coe_eq_inter_of_eqOn
#print axioms Causal.real_eqOn_inter_of_isDevelopment
#print axioms Causal.timelikeLine_isCauchySurfaceOn_Ioo_of_mem
#print axioms Causal.timelikeLine_isCauchySurfaceOn_union_Ioo
#print axioms Causal.ErsEtaleWitness.lineA_subset_top
#print axioms Causal.ErsEtaleWitness.lineA_subset_disU₂
#print axioms Causal.ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale
#print axioms Causal.ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale_doubled
#print axioms Causal.ErsEtaleWitness.twoU₁
#print axioms Causal.ErsEtaleWitness.twoU₂
#print axioms Causal.ErsEtaleWitness.twoA
#print axioms Causal.ErsEtaleWitness.twoSol₂
#print axioms Causal.ErsEtaleWitness.twoA_subset₁
#print axioms Causal.ErsEtaleWitness.twoA_subset₂
#print axioms Causal.ErsEtaleWitness.eqOn_twoSol₂
#print axioms Causal.ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale_twoPoint
#print axioms Causal.ErsEtaleWitness.timelikeLine_ers_theorem_3_45_etale_twoPoint
#print axioms Causal.ErsEtaleWitness.timelikeLine_ers_isPreconnected_inter_of_eqOn
#print axioms Causal.ErsEtaleWitness.timelikeLine_ers_isOpenEmbedding_proj_of_eqOn
