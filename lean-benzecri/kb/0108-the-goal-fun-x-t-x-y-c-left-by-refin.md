# 0108 — The goal `(fun x => t +ᵥ x) y = c` left by refining ⟨y, hy, ?_⟩ against `c ∈ t +

*Found 2026-11-28 by T-bz-c3-conjugues; recorded by the master session.*

The goal `(fun x => t +ᵥ x) y = c` left by refining ⟨y, hy, ?_⟩ against `c ∈ t +ᵥ C` does not rewrite with vadd_eq_add until it is beta-reduced: write `show _ +ᵥ _ = c` first.
