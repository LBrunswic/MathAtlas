---
id: 0006
title: The spherical models and the Thurston suspension
kind: pattern
created: 2026-11-20
---
The spherical models are `GX.RaySphere V` with `GX.SpecialOrth V` (`GX.Spherical.S3Model`);
𝕊³ = `Sph3` = `RaySphere (ℝ ⊕ (ℝ ⊕ ℂ))`, polar axes split off by `GX.PolarSum`, so the Thurston
suspension 𝕊ⁿ → 𝕊ⁿ⁺¹ is `GX.thurstonStructure` (cone charts through `GX.sphConic`, chart changes
1 ⊕ A via `GX.liftSO`). A conical model in a non-Euclidean (G,X) is `GX.polarCone`: an open
embedding j : ℂ → X conjugating z ↦ e^{iα} z to some ρ ∈ G (for 𝕊²: `GX.stereoInv`, `GX.rotSO3`);
it ports `GX.conical`, apex singular iff α ≠ 2π (T-gx-spherical-cone).
