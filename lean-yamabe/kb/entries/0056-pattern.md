---
id: 0056
title: Pattern:
kind: pattern
created: 2026-11-23
---
Found by T-yamabe-analysis (round 3). Pattern: Rellich–Kondrachov on the manifold layer is Mfd.rellich_kondrachov' (YamabeScaffold.RellichManifold): Mfd.local_cell_approx gives, per good chart and C¹ cut-off ρ, an A < ∞ with ‖ρu − Σ_{z∈Z} avg_{C_z}(chartFun (ρu)) • 1_{V ∩ φ⁻¹ C_z}‖_{L²(μ)} ≤ A·δ·w12 g μ u for every δ > 0 (Z from Half.cell_approx); the global sum runs over β = Σ _ : t, (Fin N → ℤ) with s = Finset.univ.sigma Z, split by Finset.sum_sigma, Finset.sum_sub_distrib and u = Σ ρ_i u; exists_subseq_tendsto_eLpNorm_two concludes.
