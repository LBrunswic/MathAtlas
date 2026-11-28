---
id: 0311
title: A solution-dependent causality separates hypotheses that read cau of a glued function
kind: pattern
created: 2026-11-28
---
To separate hypotheses that read `cau` of a glued function, make `cau u` the timelike line on a set `T` of functions not closed under `glueSolutions`, and the spacelike line off `T`: every development then has the timelike line, because a Cauchy surface for the spacelike line contains its open set (`Causal.spacelikeLine_subset_of_isCauchySurfaceOn`), while the glued function of two members of `T` can fall outside `T`. Always disclose `¬ CausalityFollows` (`Causal.Ers482RestartSeparation`: `restart_separation`, ERS Thm 4.82's uniform restart not implied by the conclusion; `not_causalityFollows_cauSep`).
