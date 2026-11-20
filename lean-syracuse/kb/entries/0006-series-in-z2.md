---
id: 0006
title: Series in ℤ_[2], and 1/3 as a unit
kind: pattern
created: 2026-11-20
---
Found by T-syr-rep. `Summable.of_norm_bounded summable_geometric_two` with `PadicInt.norm_units` (‖unit‖ = 1) and `PadicInt.norm_p (p := 2)` (‖2‖ = 2⁻¹); split the first term with `Summable.tsum_eq_zero_add`, pull a factor with `Summable.tsum_mul_left`. 1/3 is `↑(isUnit_three_padicInt.unit⁻¹)`, with `IsUnit.mul_val_inv`.
