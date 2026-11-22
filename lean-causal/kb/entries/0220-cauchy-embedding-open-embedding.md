---
id: 0220
title: A Cauchy embedding is an open embedding: instances on N suffice
kind: pattern
created: 2026-11-22
---
An `IsEMorphism` is continuous and open and a Cauchy embedding is injective, so `IsCauchyEmbedding.isOpenEmbedding` holds and the source inherits T1, T2 and second countability from the target (`.t2Space`, `.secondCountableTopology`, `Topology.IsEmbedding.t1Space`; `Causal.CExtConnexeSecondCountable`). A hypothesis on `M` of a Cauchy-extension lemma, such as `hcover` (`M = J⁺(Σ) ∪ J⁻(Σ)`), can then be asked of `N` only.
