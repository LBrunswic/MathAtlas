---
id: 0263
title: Prefer the T1 route to discharge CurvesExtend
kind: pattern
created: 2026-11-23
---
Levin's route (`curvesExtend_of_secondCountable hT hG`) needs Tarentin and GloballyHyperbolic binders; the T1 route (`curvesExtend_of_t1_secondCountable C`) needs only `[T1Space M] [SecondCountableTopology M]`. Three Lemma K steps (`strictJplus_eq_Jplus_chartFutureSide`, `isOpen_strictJplus_of_twoSided`, `isOpen_strictJplus_of_isCauchySplitting`) have neither, so only the T1 route gives their forms (T-abs-curves-free-lemma-k).
