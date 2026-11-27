---
id: 0205
title: inside namespace GX a bare minkQ resolves to GX.minkQ (on ℝ × ℂ), not Causal.Flat.minkQ; w
kind: pitfall
created: 2026-11-28
---
Found by T-bbs-cheminsing. inside namespace GX a bare minkQ resolves to GX.minkQ (on ℝ × ℂ), not Causal.Flat.minkQ; write it qualified, or open Causal.Flat selectively (open Causal.Flat (minkB_comm ...)). λ cannot be part of an identifier (hλ fails to parse).
