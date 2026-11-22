---
id: 0237
title: Give the point explicitly in ×ˢ membership proofs
kind: pitfall
created: 2026-11-22
---
In `×ˢ` membership proofs write `show ((a, b) : X × Y) ∈ s ×ˢ t from ⟨_, _⟩`: the anonymous constructor otherwise unifies the point with an unrelated pair whose first component matches (T-abs-gluing-models).
