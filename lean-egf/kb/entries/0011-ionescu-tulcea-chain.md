---
id: 0011
title: A homogeneous chain by Ionescu-Tulcea, and a sampler with a randomized stopping time
kind: pattern
created: 2026-11-21
---
Found by T-egf-sampling. `Kernel.trajMeasure (X := fun _ => X) μ₀ (fun n => K.comap (fun h => h ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _))`; pass `X` explicitly. A sampler with a randomized stopping time is a chain on S × Bool (`EGF.GenerativeFlow.pathLaw`, `EGF.Sampling`): the state moves by π whatever the flag, and a lowered flag is raised at the new state with probability `stop`; τ = 1 + the first raised index. A decision allowed to look ahead keeps the hazard but breaks the law of s_τ (OQ-60).
