---
id: 0256
title: Twins under different names, kept because both are cited
kind: convention
created: 2026-11-23
---
`Causal.Causality.Jplus_inter_Jminus_eq` (`Causal.CBG.Ppcm`, model-layer, used by lean-gx) and `IsAcausal.Jplus_inter_Jminus` (`Causal.CauchySeparation`, ETT) have the same type; `Remarks/SingularRowsCauchyExt`'s `causalCurveOn_`/`causalCurveIn_comp_monotoneOn` are the Type-0 instances of `CExtConnexeCauchy.SubArc`'s universe-polymorphic ones (kb/0244). Both names in each pair are cited (ledgers, lean-gx), so neither is deleted; a new proof cites the ETT-layer one.

**Update 2026-11-27 (T-abs-merge-stranded-duplicates): the first pair is merged.** `Causal.CBG.Ppcm` imports `Causal.CauchySeparation` (ETT-layer; no cycle, and neither module is in `Causal.Ladder.Rules`' closure), and `Causality.Jplus_inter_Jminus_eq` is now `hac.Jplus_inter_Jminus hcaus`: one proof, both names, same types. The SubArc/SingularRowsCauchyExt pair stays as kb/0244 says.
