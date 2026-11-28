---
id: 0334
title: Rules imports the light Causal.StrongCausalityHull, not SCOpenWithoutTarentin
kind: convention
created: 2026-11-28
---
The model-free half of strong causality's open form (the causal hull, `StronglyCausal.stronglyCausalOpen_of_causallyOpen`, the counterexample's shape) is in `Causal.StrongCausalityHull`, which imports `Causal.GlobalHyperbolicity` only; `Causal.Ladder.Rules` imports it for its one rule, so SCOpenWithoutTarentin, NestedTransfer and OneWayMembrane left Rules' closure (55 → 52 modules). The same tidy put `IsEMorphismOn.chronalCurveOn_comp` and `pastInextensible_invComp` in `Causal.CauchyExtension`, `ChronalHomotopyOn.homotopicRel` in `Causal.TimelikeHomotopy` (with `Mathlib.Topology.Homotopy.Basic`), `IsSpacetimeExtension.isEMorphismOn` in `Causal.C0ExtensionSkeleton`, and the Cauchy split `IsCauchySurfaceOn.mem_Jplus_union_Jminus` in `Causal.CurvesExtendSecondCountable` (`splitBy_of_t1_secondCountable` its corollary). Updates kb/0061's list of stranded lemmas.
