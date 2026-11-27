import CausalScaffold.Model.TimeCylinderLSC

/-! Probe for T-loc-time-cylinder-lsc: the main declarations, their axioms, and the projections
the keeper's [[fails]] entries read. Run with
`taskset -c 0-11 lake env lean -DwarningAsError=true campaign/T-loc-time-cylinder-lsc/Probe.lean`
after `lake build CausalScaffold.StronglyCausalTransport CausalScaffold.Model.TimeCylinderLSC`. -/

open Causal Causal.Flat TopologicalSpace

#check @Causal.ChartIso.causallyConvexIn_image_iff
#check @Causal.ChartIso.stronglyCausalOn_iff
#check @Causal.ChartIso.stronglyCausalOn_chartSource
#check @Causal.Causality.locallyStronglyCausal_of_chartIso
#check @Causal.Causality.locallyStronglyCausal_of_forall_chartIso_of_stronglyCausal
#check @Causal.IsCausalIso.locallyStronglyCausal_iff
#check @Causal.Flat.locallyStronglyCausal_of_chartIso_chartAt
#check @Causal.Flat.flatCausality_stronglyCausalOn_chartSource
#check @Causal.Flat.flatCausality_locallyStronglyCausal
#check @Causal.Flat.timeCylinder_separates_locallyStronglyCausal
#check @Causal.Flat.timeCylinder_zero_separates_locallyStronglyCausal

#print axioms Causal.ChartIso.causallyConvexIn_image_iff
#print axioms Causal.ChartIso.stronglyCausalOn_iff
#print axioms Causal.ChartIso.stronglyCausalOn_of_le
#print axioms Causal.ChartIso.stronglyCausalOn_chartSource
#print axioms Causal.Causality.locallyStronglyCausal_of_chartIso
#print axioms Causal.Causality.locallyStronglyCausal_of_forall_chartIso
#print axioms Causal.Causality.locallyStronglyCausal_of_forall_chartIso_of_stronglyCausal
#print axioms Causal.IsCausalIso.stronglyCausalOn_iff
#print axioms Causal.IsCausalIso.locallyStronglyCausal_iff
#print axioms Causal.Flat.locallyStronglyCausal_of_chartIso_chartAt
#print axioms Causal.Flat.flatCausality_stronglyCausalOn_chartSource
#print axioms Causal.Flat.flatCausality_stronglyCausalOn_of_le
#print axioms Causal.Flat.flatCausality_locallyStronglyCausal
#print axioms Causal.Flat.timeCylinder_locallyStronglyCausal
#print axioms Causal.Flat.timeCylinder_separates_locallyStronglyCausal
#print axioms Causal.Flat.timeCylinder_zero_separates_locallyStronglyCausal

/-- The three [[open]] entries `locally_strongly_causal → is_causal, strongly_causal,
strongly_causal_open`, at the cylinder with one space dimension, projected from the separation. -/
example : (timeCylinder 1).LocallyStronglyCausal ∧ ¬ (timeCylinder 1).IsCausal ∧
    ¬ (timeCylinder 1).StronglyCausal ∧ ¬ (timeCylinder 1).StronglyCausalOpen := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h₁, -, h₂, h₃, h₄⟩ :=
    timeCylinder_separates_locallyStronglyCausal (d := 1) le_rfl
  exact ⟨h₂, h₁, h₃, h₄⟩

/-- The same at the timelike circle, which is moreover causally compact. -/
example : (timeCylinder 0).CausallyCompact ∧ (timeCylinder 0).LocallyStronglyCausal ∧
    ¬ (timeCylinder 0).IsCausal ∧ ¬ (timeCylinder 0).StronglyCausal := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h₀, h₁, h₂, h₃, -⟩ :=
    timeCylinder_zero_separates_locallyStronglyCausal
  exact ⟨h₀, h₂, h₁, h₃⟩

/-- Two-sided: the time-reversed cylinder is locally strongly causal too. -/
example (d : ℕ) : (timeCylinder d).dual.LocallyStronglyCausal :=
  Causality.dual_locallyStronglyCausal.2 timeCylinder_locallyStronglyCausal

/-- The chart at any point of the cylinder has a source strongly causal as a spacetime. -/
example (d : ℕ) (x : TimeCylinder d) :
    (timeCylinder d).StronglyCausalOn (chartSource (chartAt (Minkowski d) x)) :=
  flatCausality_stronglyCausalOn_chartSource
    ((gxGroupoid (isom d) (Minkowski d)).subset_maximalAtlas (chart_mem_atlas (Minkowski d) x))

/-- `𝐌ⁿ` itself, through `flatCausality_self`: the instance agrees with the edge
`strongly_causal ⇒ locally_strongly_causal`. -/
example (d : ℕ) : (minkowski d).LocallyStronglyCausal := by
  have h := flatCausality_locallyStronglyCausal (d := d) (M := Minkowski d)
  rwa [flatCausality_self] at h

/-- The transport with a model per point, on the timelike line with its identity chart. -/
example : timelikeLine.LocallyStronglyCausal :=
  Causality.locallyStronglyCausal_of_chartIso fun _ =>
    ⟨ℝ, inferInstance, timelikeLine, OpenPartialHomeomorph.refl ℝ, trivial,
      chartIso_refl timelikeLine, timelikeLine_locallyStronglyCausal⟩

/-- Causal-isomorphism invariance, on the identity. -/
example : timelikeLine.LocallyStronglyCausal ↔ timelikeLine.LocallyStronglyCausal :=
  (IsCausalIso.refl timelikeLine).locallyStronglyCausal_iff
