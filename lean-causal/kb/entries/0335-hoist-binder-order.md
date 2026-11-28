---
id: 0335
title: A hoist into a module whose variable line orders binders differently changes the statement
kind: pitfall
created: 2026-11-28
---
Moving a declaration byte for byte into a namespace whose `variable` line orders the implicit binders differently changes its statement: `IsEMorphismOn.pastInextensible_invComp` placed inside `Causal.CauchyExtension`'s namespace `IsEMorphismOn` would have bound `{N} [TopN]` before `{M} [TopM]` (`campaign/T-abs-sc-open-hoist/scratch/BinderOrder.lean`: `same type: false`), so it sits in a block reopening its old scope. kb/0255 (universe parameters), extended to binder order: compare the elaborated type before and after every hoist.
