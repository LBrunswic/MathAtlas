---
id: 0005
title: A real infimum with a nonpositive lower bound needs no nonemptiness
kind: pattern
created: 2026-11-21
---
Found by T-yamabe-kobayashi. `Real.le_sInf (hs : ∀ x ∈ s, a ≤ x) (ha : a ≤ 0) : a ≤ sInf s`, since `sInf ∅ = 0` (`le_infConf`).
