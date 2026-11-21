---
id: 0129
title: A causality on a closed subspace of ℝ²: the notched plane
kind: pattern
created: 2026-11-21
---
A causality on a closed subspace of ℝ²: the notched plane. Carrier the subtype M = {u ≤ 0 ∨ v ≤ 0}, a closed down-set of the product order, so a future causal segment ENDING in M lies in M (segment_subset_Icc); a step is `a ≤ b ∧ segment ℝ a b ⊆ Subtype.val '' U`. For thickening arguments take the ambient open O with val⁻¹' O = U (isOpen_induced_iff), move the segment in O by Causal.eventually_segment_subset_of_isOpen, and come back with the down-set property (notchedPlane_segment_subset_image); points near a subtype point come from mem_nhds_subtype, and a small ε > 0 from (h.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin |>.exists. Curves into the subtype: the affine path with the parameter clamped, max 0 (min r 1) (notchedPath) (T-abs-plain-not-open).
