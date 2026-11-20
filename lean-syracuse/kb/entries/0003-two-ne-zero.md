---
id: 0003
title: ZMod 2 is a ℤ/2ℤ-ring with 2 = 0; Mathlib's multiplicity of 0 is 1
kind: pitfall
created: 2026-11-20
---
Under the printed definition ZMod 2 qualifies and has 2 = 0 (`IsZ2Ring.two_eq_zero_iff`): assume
`(2 : A) ≠ 0` wherever halves must be unique or RHS_n injective; it gives `CharZero A`. Mathlib's
ℕ-valued `multiplicity a 0 = 1` (`multiplicity_zero`), not 0: `v2 0 = 1` is a junk value. Inside
`namespace Syracuse` a local `a` or `p` shadows `Syracuse.a` / `Syracuse.p` (T-syr-base).
