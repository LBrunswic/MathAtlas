---
id: 0297
title: future_one_connected is separated both ways: no chronology gives it vacuously; winding takes it away
kind: pattern
created: 2026-11-27
---
A causality with no chronology (`∀ x y, ¬ C.lt W x y`) is future one-connected on every open set: a chronal curve over `[0, 1]` would have `γ 0 ≪ γ 1` (`Causal.Causality.futureOneConnectedOn_of_forall_not_lt`, Causal/FutureOneConnectedVacuous.lean); it is also push-up, and not causally plain (`[Nonempty M]`). So the rational, lightlike, jump and symmetric rational lines separate future_one_connected from every other node (`…_separates_futureOneConnected`). The other way, the flat cylinder ℤe₁\𝐌^{1+1} has every other node and lacks it (`Causal.Flat.spaceCylinder_separates`, Causal/Model/FlatSpaceCylinder.lean): a chronal homotopy is a mathlib homotopy of paths rel {0, 1} (`ChronalHomotopyOn.homotopicRel`), and the covering map's lifting (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`) separates curves of different winding (`windCurve_not_chronallyHomotopicOn`). The bridge reads no chronality: a hoist candidate for Causal.TimelikeHomotopy.
