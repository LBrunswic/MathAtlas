---
id: 0242
title: A continuous extension at corresponding points does not give CorrespondingCompact
kind: pitfall
created: 2026-11-23
---
On the exponential gluing the corresponding points near every point of C are the values of a continuous map (`j₂ ∘ j₁⁻¹` extended) and `CorrespondingCompact` fails at a point of `closure C \ C` (`expGluing_continuous_extension_witness`). `correspondingCompact_of_continuousOn` needs the map near every point of `closure C`, so 'A3 implies the property' is not a topological fact (T-abs-gluing-compact-def).
