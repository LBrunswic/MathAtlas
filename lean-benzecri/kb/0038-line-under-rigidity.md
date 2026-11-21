# 0038 — Pattern: the image of a line under the rigidity element

*Found 2026-11-21 by T-bz-c2-theoreme-affine; recorded by the master session.*

Pattern: the image of a line L = q₀ + ℝw of φ̃(V) under the rigidity element A, where hA : ∀ y, p (g • y) = A • p y and p M = q₀, is the line φ̃(gM) + ℝ (A.linear w). Prove it with `rw [hA N, hN, hA M, hM, affineEquiv_smul_def, affineEquiv_smul_def, A.map_vadd, map_smul, vadd_eq_add]`. To show a sub-segment [q, t•u + q] lies on that line, use segment_eq_image' and convert. Then `show` the beta-reduced goal before `rw [add_sub_cancel_right, smul_smul, add_comm]`: the lambda blocks smul_smul otherwise.
