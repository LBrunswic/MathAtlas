---
id: 0239
title: Stabilizer of a spacelike vector in SO_0(1,2) is abelian (GX.BTZAdm.frame_commute_of_fix);
kind: pattern
created: 2026-11-28
---
Found by T-btz-linear-part-faithful. Stabilizer of a spacelike vector in SO_0(1,2) is abelian (GX.BTZAdm.frame_commute_of_fix); the swap of the two null lines is excluded by a det computation in the null-frame basis (rw [<- LinearMap.det_toMatrix F.basis, Matrix.det_fin_three]; simp only [F.toMatrix_apply, frameCoord, Matrix.cons_val_*]).
