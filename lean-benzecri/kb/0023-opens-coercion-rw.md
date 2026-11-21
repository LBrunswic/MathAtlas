# 0023 — Pitfall: `rw` with an image under `Subtype.val` on `Opens` can fail

*Found 2026-11-21 by T-bz-c2-cas-affin; recorded by the master session.*

On a subtype of `TopologicalSpace.Opens`, `rw [himg]` with `himg : Subtype.val '' U = …` can fail
after `rw [← IsInducing.subtypeVal.isPreconnected_image]`, because the coercion differs
syntactically. Use `convert h using 1; ext` instead.
