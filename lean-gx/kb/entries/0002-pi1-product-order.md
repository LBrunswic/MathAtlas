---
id: 0002
title: mathlib's π₁ product runs the right factor first
kind: pitfall
created: 2026-11-20
---
mathlib's `FundamentalGroup` is `End` in the fundamental groupoid: `fromPath [p] * fromPath [q] =
fromPath [q.trans p]`, the right factor runs first. Say so whenever an ordered product of loops is
stated, and fix where the cyclic order starts (T-3p1-theorem-m, `GXScaffold.Interaction`).
