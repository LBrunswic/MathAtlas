---
id: 0185
title: An open subset of a singular (G,X)-manifold is one, and of an E₀-manifold an E₀-manifold
kind: pattern
created: 2026-11-21
---
With `opensSingularGXStructure`, the inclusion is an `IsAEChart` in one line: `isAEChart_of_isAEMorphism_of_isLocalHomeomorph (isAEMorphism_opensSingular_val U) U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph rfl` (`Causal.CupCapBTZCounterexample.isAEChart_subtypeCoe`); composing with M's charts gives `E0Covered U` (`e0Covered_opens`) (T-ett-cupcap-btz-cex).
