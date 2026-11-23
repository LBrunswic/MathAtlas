---
id: 0054
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-i-pm. Pitfall: inside namespace GX, minkQ resolves to GX.minkQ (Singular/Quotient, on ℝ × ℂ). Write Causal.Flat.minkQ, and never `open Causal.Flat (minkQ)`.
