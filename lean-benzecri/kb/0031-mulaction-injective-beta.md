# 0031 — Pitfall: after apply MulAction.injective γ the goal is a beta-redex

*Found 2026-11-21 by T-bz-c2-theoreme; recorded by the master session.*

After `apply MulAction.injective γ` the goal is `(fun x => γ • x) a = (fun x => γ • x) b`, and `rw [← hγ]` finds nothing. Run `show γ • a = γ • b` first.
