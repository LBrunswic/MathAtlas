---
id: 0057
title: Pattern:
kind: pattern
created: 2026-11-23
---
Found by T-yamabe-analysis (round 3). Pattern: a locally-Lebesgue μ is IsLocallyFiniteMeasure (Mfd.isLocallyFiniteMeasure_of_isLocallyLebesgue: interior U ∩ (chart source ∩ φ⁻¹ ball(φ x₀, 1)) has μ ≤ C·vol(ball)), so on a compact M `infer_instance` gives IsFiniteMeasure μ (CompactSpace.isFiniteMeasure through isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure): Mfd.isFiniteMeasure_of_isLocallyLebesgue. The [IsFiniteMeasure μ] binders of Mfd.Reads.rellichProp, Reads.constLimit, Reads.lem_positivity, Reads.cor_negative and Mfd.lem_positivity are derivable from hμ.
