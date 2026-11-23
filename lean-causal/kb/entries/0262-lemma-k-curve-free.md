---
id: 0262
title: Lemma K's family has a curve-free form of each of its 31 curve theorems
kind: pattern
created: 2026-11-23
---
Since T-abs-curves-free-lemma-k, each of the 31 `hext : C.CurvesExtend` theorems of `Causal.LemmaKBare`, `LemmaKReduction`, `LemmaKSC`, `LemmaKLocal`, `LemmaK` has a second countable form: 24 in `Causal.CurvesFreeLemmaK.{Bare,Reduction,SC,Local}` (name + `_secondCountable`; `isCauchySurface_iff_of_curvesExtend` → `isCauchySurface_iff_of_secondCountable`), 7 earlier (`Causal.LevinUtility`, `Causal.LemmaKSCLocal`'s `_of_secondCountable`, and LemmaK's lemma of record `isCauchySurface_of_isLocallyCauchy_of_causallyOpen`). No curve binder of the strict `Causal.*` library is left without a form: ErsUnions/ErsMughd and `Causal.Ladder.Dual` were covered already (kb/0260, T-abs-curves-free-ers-unions).
