---
id: 0012
title: Total variation without SignedMeasure: tvDist := tvMass/2
kind: pattern
created: 2026-11-21
---
Found by T-egf-sampling. For finite measures `EGF.tvDist := tvMass/2`; for equal masses it is (μ − ν)(S) (`EGF.sub_univ_eq_sub_univ`), and `EGF.tvDist_eq_iSup` gives sup_A abs(μ(A) − ν(A)). Without the ½ the negative-control bound is false (`EGF.TwoPoint.negative_control_sharp`).
