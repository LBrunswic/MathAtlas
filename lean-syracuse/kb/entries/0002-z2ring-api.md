---
id: 0002
title: The ℤ/2ℤ-ring API, and the total maps with a junk value at −1/3
kind: pattern
created: 2026-11-20
---
`IsZ2Ring A` = `IsDomain` + `IsNoetherianRing` + `Nonempty (A ⧸ span{2} ≃+* ZMod 2)` (`Syracuse.Valuation`),
instances ℤ, ℤ_[2], ZMod 2. `Syracuse.T`, `a`, `p` (`Syracuse.Base`) are total on A with a junk value where
3x + 1 = 0 (x = −1/3, possible only when 3 ∈ Aˣ, e.g. ℤ_[2]); `base` holds unconditionally, `base_of_orbit`
and `base_of_not_isUnit_three` give the paper's meaning. Every statement that needs the paper's meaning
names its hypothesis (OQ-42) (T-syr-base).
