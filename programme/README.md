# The ETT programme

ETT is a **reasoning system for causality**. It does not set out to give metric-free versions of
known theorems. Every result handled here is factored into four layers:

1. **Global argument (causal-topological).** A theorem of ETT, proved in any topological spacetime
   from causality properties alone. It lives in `lean-causal/Causal/` and never imports a metric.
2. **Localisation property.** The local, checkable property the global argument needs, for example
   rigidity on connected opens, no corresponding boundary points, a boundary chart with sandwiched
   cones, future one-connectedness, or a nesting of two causalities. It is a node or an edge
   hypothesis of the ladder.
3. **Geometric proof of the localisation.** A lemma per model class (Minkowski, flat (G,X), E_α,
   E_0, C⁰ metrics, …) proving the localisation property by geometry or PDE.
4. **Classification criteria.** Cases are sorted by which causal-topological property holds:
   sub- or superluminal nesting, connected overlaps, corner extensions, push-up, singular line
   kept or removed.

The programme's objects are:

| file | what | kept by |
|---|---|---|
| `ladder.toml` | the hierarchy (a DAG) of causality properties: nodes, implications with Lean witnesses and side conditions, non-implications with counterexamples, and the consequences valid at each level | ladder-keeper; checked by `tools/ladder.py` |
| `roadmap.toml` | the programme's targets: `abstract` (layer 1), `localisation` (layer 3, one per model), `ladder`, `binder`, `tactic`, `publish`, `package` | programme-planner; checked by `tools/roadmap.py --file programme/roadmap.toml` |
| `papers/<sbierski-slug>/certificate/binder.toml` | the **binder** of each ledgered Sbierski paper: every row split into its ETT theorem (layer 1), its localisation properties (ladder ids) and its geometric lemma for his metric class (layer 3) | programme-planner; checked by `tools/binder.py` |
| `JOURNAL.md` | one entry per `/ett-programme` iteration | the loop |

The loop is `.claude/skills/ett-programme/SKILL.md`. It shares the checkout with `/atlas-team` through
leases (`tools/lease.py`). The source of the programme is the review `references/sbierski/SYNTHESIS.md`
and the author's framing of 2026-11-20 recorded above.
