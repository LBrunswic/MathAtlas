# 0092 — Destructuring x ∈ s + t after `rw [h]`, where h unfolds a def into a Minkowski s

*Found 2026-11-28 by T-bz-c3-fibres; recorded by the master session.*

Destructuring x ∈ s + t after `rw [h]`, where h unfolds a def into a Minkowski sum, leaves a beta-unreduced `(fun x1 x2 => x1 + x2) a b`. Write `rw [h, Set.mem_add] at hx` before obtain/rintro.
