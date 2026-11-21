---
id: 0018
title: The KL-weakFM loss: KL between densities, computable KLs on Bool, the reversed flow
kind: pattern
created: 2026-11-21
---
Found by T-egf-loss. KL between densities: `Measure.rnDeriv_eq_div`, `rnDeriv_smul_left_of_ne_top`
and `rnDeriv_withDensity` give `llr κ (c • f λ) = log k − log f − log c` κ-a.e.; `toReal_klDiv_of_measure_eq`
turns `klDiv` into that integral (`EGF.llr_normalize_kappaHat_ae`, `EGF.kl_decomposition`). Two
computable KLs on `Bool` refute an identity by `2⁸ ≠ 3⁵` through `Real.log_injOn_pos`. Against the
counting measure on `Bool`: `EGF.rnDeriv_count_bool` (`μ.rnDeriv count b = μ{b}`), `integral_count`,
`EGF.integral_bool`; `Integrable.of_finite` discharges every integrability hypothesis. The
continuation probability in densities is `EGF.cont_ae_eq_ratio`; a flow reversed along a backward
policy is `EGF.GenerativeFlow.reverse`, flow matching from `κ̂` to `F_init + δF_init`
(`EGF.reverse_isFlowMatching_iff`; what Algorithm 1's backward buffer holds is OQ-83). Pitfalls:
`λ` is a keyword (no identifier `hKλ`); a `rw` with an implicit point argument rewrites every
instance once unified, so repeating it fails (use `simp only`); `rw [eq_withDensity_dens hinit]`
rewrites every `Finit`, also inside densities (use `congrArg₂ (· + ·) h1 h2`);
`integral_eq_lintegral_of_nonneg_ae` and `hasFiniteIntegral_iff_ofReal` need `(f := …)` for a
named density.
