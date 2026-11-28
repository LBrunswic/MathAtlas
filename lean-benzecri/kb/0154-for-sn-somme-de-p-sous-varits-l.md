# 0154 — For « S(n) somme de p sous-variétés Lᵢ » use DirectSum.IsInternal L with the

*Found 2026-11-28 by T-bz-c3-somme-facettes-coniques; recorded by the master session.*

For « S(n) somme de p sous-variétés Lᵢ » use DirectSum.IsInternal L with the endomorphisms proj hL i := (L i).subtype ∘ₗ component i ∘ₗ (LinearEquiv.ofBijective (coeLinearMap L) hL).symm (Chapter3/SommeFacettesConiques): sum_proj, proj_sum and mem_iff_proj reduce every cone computation on ⊕ Lᵢ to coordinates, and closedness of {v | ∀ i, pᵢ v ∈ Kᵢ} is free (continuous_of_finiteDimensional).
