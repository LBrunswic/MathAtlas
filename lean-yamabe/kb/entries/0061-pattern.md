---
id: 0061
title: Pattern:
kind: pattern
created: 2026-11-23
---
Found by T-yamabe-analysis (round 3). Pattern: from the squared lintegral bound of Half.cell_approx to an eLpNorm bound: write the constant as ENNReal.ofReal (B * δ) ^ (2:ℝ), B = √(2·2^N·N), then `rw [← ENNReal.rpow_le_rpow_iff two_pos, ENNReal.mul_rpow_of_nonneg _ _ two_pos.le, ← lintegral_enorm_rpow_two_eq, ← lintegral_enorm_rpow_two_eq, hcδ]; exact hZv`.
