---
id: 0136
title: isClosed_sing and interior_sing are already strict for every singular (G,X)-manifold
kind: pitfall
created: 2026-11-21
---
Do not re-derive them: `Causal.isClosed_sing G X M` and `(Causal.isSkeletal_sing G X M).interior_eq_empty` (`Causal.Port.SingularAtlas`) give `isClosed_sing` and `interior_sing` of `SingularFlatAxioms` for every singular `(G,X)`-manifold. Local compactness and no isolated point come from charts alone (`SFATransfer.exists_isCompact_nhds_of_chart`, `nhdsNE_neBot_of_chart`); metrizability is `infer_instance` from T2, second countable and locally compact (T-ett-sfa-local-e0).
