---
id: 0247
title: model_path shows one shortest chain: check each direct import before a hoist
kind: pitfall
created: 2026-11-23
---
`tools/ladder.py`'s `model_path` returns one shortest import chain to a model, not every one. Before planning a hoist, take `model_path` of each direct import of the module: `Causal.LemmaKBare`'s evidence showed only `Model.CurvesExtendModels`, but `Model.Massive` and `Causal.Splitting` → `Flat.IsomCausal` also made it model-layer (T-abs-hoist-lemma-k).
