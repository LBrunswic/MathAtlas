---
id: 0008
title: `(T^[n] x : ℝ)` iterates T over ℝ: write `((T^[n] x : ℤ) : ℝ)`
kind: pitfall
created: 2026-11-20
---
Found by T-syr-integer-bounds. With x : ℤ, `(T^[n] x : ℝ)` elaborates as `T^[n] (↑x : ℝ)`, the map over ℝ (T needs only a commutative ring), and silently changes the statement. Write `((T^[n] x : ℤ) : ℝ)`.
