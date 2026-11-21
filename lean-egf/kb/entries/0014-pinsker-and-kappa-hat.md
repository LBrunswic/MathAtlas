---
id: 0014
title: Pinsker with Mathlib's klDiv: EGF.pinsker; inference at κ̂
kind: pattern
created: 2026-11-21
---
Found by T-egf-sampling-corollaries. Mathlib has `klDiv` but no Pinsker at this pin: `EGF.pinsker` (`EGF.SamplingCorollaries`) gives TV(μ ‖ ν) ≤ (klDiv μ ν / 2)^{1/2} in [0, ∞] for probability measures, from the verbatim port `EGF.Pinsker.*` of GFNBounds' ILBoundFull. At F_term := (F_init + F_in − F_out)⁺ the terminal error vanishes and `virtualTerm = κ̂` (`EGF.virtualTerm_kappaHat`), so `main_quantitative_sampling` at F_term := κ̂ is the inference bound.
