# 0011 — Do not prefix a lemma name with `IsCompact.` inside `namespace Benzecri`

*Found 2026-11-20 by T-bz-c2-projection; recorded by the master session.*

A lemma named `IsCompact.foo` inside `namespace Benzecri` becomes `Benzecri.IsCompact.foo`, and
`hE.foo` fails, because `IsCompact` unfolds to a `∀` (lean-causal kb/0010). Name such lemmas without
the prefix (`exists_uniform_chart_radius`).
