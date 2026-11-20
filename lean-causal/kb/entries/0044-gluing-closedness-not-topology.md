---
id: 0044
title: Closed H, open C and a unique corresponding point are not topology
kind: pitfall
created: 2026-11-20
---
Of the facts about corresponding boundary points used in maximal-development proofs, only the
closedness of the set of corresponding PAIRS is topological (`Gluing.isClosed_correspondingPairs`).
Chruściel's "H is closed" fails for ℝ² glued along (a, c) ↦ (a, eᶜ) (`not_isClosed_nonHausdorffLeft_expGluing`);
Sbierski's uniqueness of the corresponding point and openness of C in ∂U fail for the shear
(a, c) ↦ (a, a·c) (`shearGluing_not_unique`, `shearGluing_not_isOpen_in_frontier`). Treat them
as localisation properties (layer 3), or assume compactness (`isClosed_nonHausdorffLeft_of_isCompact`).
OQ-40 (T-abs-gluing-hausdorff).
