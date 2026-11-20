---
id: 0029
title: A BTZ point never witnesses a failure of causal plainness
kind: pitfall
created: 2026-11-20
---
Under `SingularFlatAxioms`, Int J⁻_U(A) = ∅ for every open U and every A ⊂ sing₀
(`SingularFlatAxioms.interior_Jminus_eq_empty`, `btz_causallyPlain_past`,
`Causal/Remarks/BTZPoints.lean`): the BTZ defect (I⁻(p) = ∅ while J⁻(p) is a half-line) sits in a
set with empty interior, so the plainness inclusion Int J⁻ ⊂ closure I⁻ holds there trivially.
Do not look for a counter-example to `defi:causalement_plat` at a BTZ point; the paper's
`rem:pas_plat` (ii) claims one, which is a recorded finding (T-ett-unanchored).
