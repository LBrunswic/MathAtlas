---
id: 0038
title: Non-local relations leave causal curves, inextensibility and Cauchy surfaces unchanged
kind: pitfall
created: 2026-11-20
---
A causality on ℝ which goes up and contains the timelike line's relations has the timelike line's
curves (`DensWitness.causalCurveIn_iff_timelike`, `Causal.CBG.SubExtensionAbstract`). Non-local
relations act only through global hyperbolicity and the strong-morphism conditions; that is how
they refute the abstract `cauchy_pgcd` (`not_cauchyPgcdAbstract`). They give no direct handle on a
curve conclusion such as `exists_mem_image_inf`, whose hypotheses (GH, `IsEMorphism`) do depend on
them (T-ett-subextension).
