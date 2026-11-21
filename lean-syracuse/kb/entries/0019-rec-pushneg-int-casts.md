---
id: 0019
title: `rec` is a keyword; `push_neg` is deprecated; `Periodic.int_mul` leaves ((q : ℤ) : ℤ) casts
kind: pitfall
created: 2026-11-21
---
Found by T-syr-upper-bounds. Do not name a hypothesis `rec`, which is a keyword: use `hrec`. In Mathlib v4.31.0, `push_neg` warns that it is deprecated (an error under `warningAsError`): use `push Not`. `Function.Periodic.sub_int_mul_eq` and `Function.Periodic.int_mul` at f : ℤ → _ produce ((q : ℤ) : ℤ) casts: clear them with `simp only [Int.cast_id]` before `rw`.
