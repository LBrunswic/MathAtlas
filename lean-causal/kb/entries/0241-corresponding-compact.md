---
id: 0241
title: DEC-160's gluing compactness is Gluing.CorrespondingCompact
kind: pattern
created: 2026-11-23
---
The gluing compactness of DEC-160 is `Causal.Gluing.CorrespondingCompact j₁ j₂` (`Causal.GluingCompact`; the X side; the Y side is `CorrespondingCompact j₂ j₁`). It is `Iff.rfl` to the inline hypothesis of `isClosed_nonHausdorffLeft_of_isCompact`; for weakly locally compact X it is properness of the projection of `correspondingPairs` onto X (`correspondingCompact_iff_isProperMap`). State new gluing theorems with it, not with the inline ∀-form.
