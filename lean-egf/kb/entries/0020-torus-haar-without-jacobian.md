---
id: 0020
title: Haar measure on UnitAddTorus without a Jacobian; the global probability instance on UnitAddCircle
kind: pattern
created: 2026-11-22
---
Found by T-egf-families. A continuous surjective group endomorphism of `UnitAddTorus d` preserves
Haar measure with no Jacobian: `Measure.isAddHaarMeasure_map_of_isFiniteMeasure` makes the image a
Haar measure, `Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure` identifies it
(`EGF.measurePreserving_torusLin`); translations by `measurePreserving_add_right`. Mathlib's
`IsProbabilityMeasure (volume : Measure UnitAddCircle)` is local to
`Analysis/Fourier/AddCircleMulti` (its `mFourier`/L² lemmas go through `haarAddCircle` and a local
`MeasureSpace`, not the global `volume`); `EGF.isProbabilityMeasure_volume_unitAddCircle`
(`EGF/TorusFamilies.lean`) provides it globally: import it rather than re-declaring it.
