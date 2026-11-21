---
id: 0135
title: I⁻(p) = ∅ at a BTZ point is not a chart fact: it uses absolute minimality
kind: pitfall
created: 2026-11-21
---
`Z⁺`, tarentin, `Z⁻` off `S` and `past_local` are chart facts (`Causal.SFATransfer`). `I⁻(p) = ∅` at a BTZ point is not, in general: a `ChartIso` constrains the relations of the open subsets of its source, hence `≪_M` only when one chart's source is all of `M`. Use absolute minimality (`SFATransfer.Iminus_eq_empty_of_cover`) with a cover whose members through `p` are sources of charts into `E₀` (sources of maximal-atlas charts lie in `Reg(M)`). `topTotal D` (`D` on every open set but `M`, every pair related at `M`) is a cheap non-minimal, non-causal witness with one isomorphic chart at each point: `Causal.SFALocalE0.e0_topTotal_separates` (T-ett-sfa-local-e0).
