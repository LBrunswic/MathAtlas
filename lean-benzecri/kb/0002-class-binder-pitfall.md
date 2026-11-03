# 0002 — A class-typed binder inside a statement becomes a local instance

*Found 2026-11-03 by the wave-3 author (WP-45n, `Cone/Base`); recorded by the master session.*

In a statement such as

    ∀ cs : ChartedSpace X M, … → @maximalAtlas … cs … = (G).maximalAtlas M

the binder `cs : ChartedSpace X M` is a **local instance** for the rest of the statement, so the
right-hand side's implicit `ChartedSpace` is resolved to `cs` as well: the "uniqueness" clause
silently reads `maxAtlas cs = maxAtlas cs` and is trivially true. Fix: name the other structure
explicitly on both sides (`@maximalAtlas … cs …` vs `@maximalAtlas … cs₀ …`), or bind the
competitor as a non-instance (`(cs : ChartedSpace X M)` used only through `@`).

**Auditors:** for every uniqueness/comparison statement that quantifies over a class-typed
structure, print it with `set_option pp.explicit true` and check that both sides carry the
intended instances.
