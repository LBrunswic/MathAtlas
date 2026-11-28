---
id: 0328
title: Cauchy surfaces of translated intervals and of two disjoint intervals on the timelike line
kind: pattern
created: 2026-11-28
---
On the timelike line `{c}` is a Cauchy surface of every bounded `]a, b[ ∋ c` (`Causal.timelikeLine_isCauchySurfaceOn_Ioo_of_mem`: kb/0308's lemma translated by `timelikeLine_isCausalIso_addRight` and `IsCausalIso.isCauchySurfaceOn_image`), and `{s, t}` is one of `]a, b[ ∪ ]c, d[` when `a < s < b ≤ c < t < d` (`timelikeLine_isCauchySurfaceOn_union_Ioo`; `Causal.ErsEtaleMghdWitnesses`). `Causal.ErsSCWitnesses` reaches `Causal.CExtConnexeCauchy.SubArc` through `CExtConnexeCauchy.Basic`, so a module that must avoid SubArc uses these instead of its `isCauchySurfaceOn_Ioo_center` and `twoIntervals`.
