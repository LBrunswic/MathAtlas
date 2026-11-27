---
id: 0180
title: Sigma* Cauchy in Reg M needs neither compactness nor finiteness
kind: pattern
created: 2026-11-27
---
Found by T-btz-reg-complete-cauchy. Sigma* Cauchy in Reg M needs neither compactness nor finiteness: GX.E0SpearFamily.LFSurgeryData.isCauchySurface_sigmaStar takes (IsCauchySurface S) and a locally finite family. Finiteness is replaced by LocallyFinite.closure_iUnion / isClosed_iUnion and eventually_all_finite. Compactness of S is replaced by cauchy_facts_lf: J^±(S) closed (E0LM.sfa_isClosed_*_cauchy) and J^∓(p) ∩ S compact (GloballyHyperbolic.isCompact_J*_inter_of_isCauchySurface with E0LM.e0_timeFunction).
