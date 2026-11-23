---
id: 0065
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-photon-circles. Pitfall: with h : σ ∈ S for a set S := {σ | 0 ≤ f σ}, the ascription (h : 0 ≤ f σ).lt_or_eq still fails, because dot notation reads the inferred type. Restate it as have h' : 0 ≤ f σ := h.
