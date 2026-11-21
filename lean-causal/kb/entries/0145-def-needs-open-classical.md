---
id: 0145
title: A def needs open Classical for dif_pos
kind: pitfall
created: 2026-11-21
---
a noncomputable def with `if h : t ∈ I then … else …` on an arbitrary Set needs `open Classical in` before it, or `dif_pos` fails with 'failed to synthesize Decidable (t ∈ I)' (Causal.intervalMap).
