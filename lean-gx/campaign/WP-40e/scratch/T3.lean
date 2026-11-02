import GXScaffold.Branched.GaloisExamples

noncomputable section
open Set Filter Topology Function unitInterval
namespace GX
attribute [local instance] Classical.propDecidable

/-- The point `(cos t, sin t, 0, 0)` of the great circle `GX.greatCircle3`. -/
def standardCirclePt (t : ℝ) : Sphere3 :=
  ⟨!₂[Real.cos t, Real.sin t, 0, 0], by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_four]
    simp [Real.cos_sq_add_sin_sq]⟩

theorem continuous_standardCirclePt : Continuous standardCirclePt := by
  refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)) _
  fin_cases i <;> simp <;> fun_prop

/-- **The standard (tame) Cantor set of `S³`**: the middle-third Cantor set of `[0, 1]`, wrapped
on the great circle by `t ↦ (cos t, sin t, 0, 0)`. -/
def standardCantor3 : Set Sphere3 := standardCirclePt '' cantorSet

theorem standardCantor3_subset : standardCantor3 ⊆ greatCircle3 := by
  rintro _ ⟨t, -, rfl⟩
  exact ⟨by simp [standardCirclePt], by simp [standardCirclePt]⟩

theorem standardCirclePt_injOn : InjOn standardCirclePt cantorSet := by
  intro a ha b hb h
  have h0 := congrArg (fun y : Sphere3 => (y : EuclideanSpace ℝ (Fin 4)) 0) h
  simp only [standardCirclePt] at h0
  simp at h0
  have hI : ∀ x ∈ cantorSet, x ∈ Icc 0 Real.pi := fun x hx =>
    ⟨(cantorSet_subset_unitInterval hx).1,
      (cantorSet_subset_unitInterval hx).2.trans (by linarith [Real.pi_gt_three])⟩
  exact Real.injOn_cos (hI a ha) (hI b hb) h0

theorem standardCantor3_isCantorSubset : IsCantorSubset standardCantor3 := by
  haveI : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  exact ⟨(Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn standardCirclePt cantorSet standardCirclePt_injOn)
    ((continuous_standardCirclePt.comp continuous_subtype_val).subtype_mk _)).symm⟩

/-- **Antoine's necklace is not tame in the classical sense** (from the residual alone,
sorry-free): no homeomorphism of `S³` carries it onto the standard Cantor set. (Classically tame
means ambiently homeomorphic to `GX.standardCantor3`; `GX.IsWildCantor` is the stronger
"carried INTO no great circle".) -/
theorem antoineNecklace_not_tame_of (hres : AntoineMeridianEssential) :
    ¬ ∃ h : Sphere3 ≃ₜ Sphere3, h '' antoineNecklace = standardCantor3 := by
  rintro ⟨h, e⟩
  exact (isWildCantor_antoineNecklace_of_res hres).2 ⟨h, e ▸ standardCantor3_subset⟩

/-- Antoine's necklace is not tame; rests on the residual `GX.antoineMeridianEssentialTop`
only. -/
theorem antoineNecklace_not_tame :
    ¬ ∃ h : Sphere3 ≃ₜ Sphere3, h '' antoineNecklace = standardCantor3 :=
  antoineNecklace_not_tame_of antoineMeridianEssential

end GX
