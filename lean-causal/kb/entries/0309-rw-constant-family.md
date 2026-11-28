---
id: 0309
title: A constant causality family defeats rw: unfold by term or by show
kind: pitfall
created: 2026-11-28
---
With a constant causality family (`cau82 := fun _ => timelikeLine`), `rw [timelikeLine_le] at h` fails on `h : (cau82 u).le U x y`, because `rw` matches syntactically. Use `timelikeLine_le.1 h` in term mode (definitional unfolding), or `show timelikeLine.…` first (`Causal.Ers482Solution`).
