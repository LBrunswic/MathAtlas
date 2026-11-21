---
id: 0011
title: The 2-adic topology and the completion as ℤ₂
kind: pattern
created: 2026-11-21
---
Found by T-syr-completion. State with `[TopologicalSpace A] (hA : IsAdic (Ideal.span {2}))`; `hasBasis_nhds_two` gives the balls {y | 2ⁿ ∣ y − x}, `continuousAt_iff_two` the ε–δ form; ℤ_[2] satisfies it (`isAdic_padicInt`); `WithIdeal ⟨span {2}⟩` is the canonical instance. `UniformSpace.Completion A ≃+* ℤ_[2]` is `RingEquiv.ofBijective (Completion.extensionHom ι hc) (Completion.cPkg.compareEquiv pkg).bijective` (the two functions are defeq); annotate `compareEquiv` as `Completion A ≃ᵤ ℤ_[2]`.
