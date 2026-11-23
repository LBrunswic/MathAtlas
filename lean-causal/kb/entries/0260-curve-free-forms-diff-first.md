---
id: 0260
title: Before planning a curve-free batch, diff the originals against existing forms
kind: pattern
created: 2026-11-23
---
Of T-abs-curves-free-cauchy's 45 curve binders, 26 already had a second countable form elsewhere (`Causal.CExtConnexeSecondCountable`, `Causal.CurvesExtendSecondCountable`, `Causal.CauchySeparation`, `Causal.ErsSecondCountable`), some stronger than the original less the binder. Diff by elaborated binder lists (kb/0227) before scoping a batch. After it, the ETT-layer CurvesExtend binders still without a form were thought to be in the Lemma K modules (T-abs-curves-free-lemma-k), ErsUnions/ErsMughd and `Causal.Ladder.Dual`; ErsUnions/ErsMughd and Ladder.Dual were in fact covered already (`Causal.Ers464SecondCountable`, `Causal.ErsSecondCountable`, `CurvesExtend.dual_secondCountable`; T-abs-curves-free-ers-unions, 2026-11-23). Since then every `CurvesExtend(On)` binder of the strict `Causal.*` library (123 ETT-layer modules: 90 binders in 18 modules) has a covering second countable form, checked by the kernel (lean-causal/campaign/T-abs-curves-free-ers-unions/). The scaffold's `CausalScaffold.SubExtension` keeps two, on statements resting on a `sorry`.
