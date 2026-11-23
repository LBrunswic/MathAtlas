---
id: 0051
title: pattern:
kind: pattern
created: 2026-11-23
---
Found by T-perf-main. pattern: the larger eigenvalue of [[p, q], [q, r]] with q >= 0. Work with the explicit root Lambda = (p+r+s)/2: (Lambda-p)(Lambda-r) = q^2, and the form bound follows from (sqrt(Lambda-p) x - sqrt(Lambda-r) y)^2 >= 0. det(M - mu 1) is Matrix.det_fin_two and then simp with Matrix.cons_val_zero/one (Yamabe.quad_le_lamMax, lamMax_largest_eigenvalue).
