---
id: 0026
title: Fourier analysis on the torus with the global volume
kind: pattern
created: 2026-11-22
---
Found by T-egf-tori-minimal (`EGF/ToriMinimal.lean`). Mathlib's `AddCircleMulti` lemmas
(`mFourierCoeff`, `hasSum_mFourier_series_L2`, `hasSum_sq_mFourierCoeff`, `coeFn_mFourierLp`) are
elaborated against a local `MeasureSpace UnitAddCircle := haarAddCircle`, not the global `volume`.
Bridge with `EGF.volume_unitAddTorus_eq_pi_haar` (`rw [← h]; rfl` with
`h : volume = haarAddCircle` from `volume_eq_smul_haarAddCircle`); transport `MemLp` by `hmu ▸ hf` to
`Measure.pi (fun _ => haarAddCircle)`, build the `Lp` elements there with `MemLp.toLp`, and identify
the coefficients of `toLp f` with those of `f` by `integral_congr_ae` — never rewrite a measure
inside an `Lp` type. `EGF.mFourierCoeff_eq_integral_volume` and `EGF.mFourier_apply_eq_toCircle`
(`e_k(x) = toCircle (∑ kᵢ xᵢ)`) turn every character identity into one in `ℝ/ℤ`.
