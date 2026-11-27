import Causal.PlainnessModels.KCalcul
import Causal.PlainnessModels.LorentzForm
import Causal.PlainnessModels.LipschitzModel
import Causal.PlainnessModels.LipschitzPushUp
import Causal.PlainnessModels.Lorentzian

/-!
# Causal plainness for the models (DEC-168): `prop:K_calcul` and `cor:K_lorentzien`

Target `T-ett-plainness-models` (`roadmap/roadmap.toml`). The umbrella of five modules:

* `KCalcul` — `prop:K_calcul` (marked there) — `ETT.tex:1557`, at every `E_{≥0}`-manifold through causal
  plainness (`SFALocal.causallyPlain`) and `prop:tarentin_fort_K`, the printed route; DEC-168's
  singular models are plain by reuse (`models_causallyPlain`).
* `LorentzForm`, `LipschitzModel`, `LipschitzPushUp`, `Lorentzian` — `cor:K_lorentzien` —
  `ETT.tex:884`, at every Lipschitz Lorentzian manifold (the reading of OQ-28 under DEC-168):
  the causality of a locally Lipschitz time-oriented Lorentzian metric on `ℝ^{1+n}` has push-up
  and is causally plain; through charts, so is every such manifold, and `K^± = I^±`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
