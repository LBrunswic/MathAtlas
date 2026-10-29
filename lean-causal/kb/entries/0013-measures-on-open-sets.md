---
id: 0013
title: A measure on an open U is a measure on M with μ Uᶜ = 0
kind: convention
created: 2026-10-29
---
The corollary of kb/0001 for measures: "U carries a measure admissible in the past" is
`AdmissiblePastOn U ν`, a `Measure M` with `ν Uᶜ = 0` and the properties read with `≤_U`, `J⁻_U`,
`K⁻_U` (`Causal/MeasureLocal.lean`). The subtype appears only in the bridge lemmas
(`admissiblePastOn_map_subtype_iff`, `regular_map_subtype_val`, `R1Space`). A countable sum of
regular measures of finite total mass is regular (`Causal.regular_sum`); outer regularity alone
does not pass to the sum.
