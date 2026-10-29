---
id: 0008
title: Membership in `V ⊓ W` and transport along `≤` of open sets
kind: pattern
created: 2026-09-27
---
## Do
* `x ∈ V ⊓ W` is proved by `⟨hxV, hxW⟩`.
* From `h : x ∈ V ⊓ W` to `x ∈ V`: `(inf_le_left : V ⊓ W ≤ V) h`.
* `hVU : V ≤ U` applies to a membership: `hVU hx`.
* `V ⊓ U = V` from `hV : V ≤ U`: `inf_eq_left.2 hV`; `(V ⊓ U) ⊓ O = (V ⊓ O) ⊓ U`:
  `inf_right_comm`.
* An open set from a set: `⟨interior N, isOpen_interior⟩ : Opens M`.
