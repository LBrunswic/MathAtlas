# Knowledge base — working in `lean-causal`

What working in this library is like: conventions, patterns, pitfalls. Read before you start;
propose an entry when you finish, if you learned something the next session would otherwise
rediscover. One fact per entry.

| id | kind | entry |
|---|---|---|
| [0001](entries/0001-open-sets-not-subtypes.md) | convention | Everything is indexed by an open set; no subtype of `M` in a statement |
| [0002](entries/0002-past-from-future-dual.md) | pattern | Prove the future statement, get the past one from `C.dual` |
| [0003](entries/0003-induction-generalizes-hypotheses.md) | pitfall | `induction h` on `TransGen` rewrites every hypothesis mentioning the endpoint |
| [0004](entries/0004-names-at-this-pin.md) | pitfall | Deprecated and renamed lemmas at mathlib `fabf563a`; a deprecation is a build failure |
| [0005](entries/0005-build-your-own-module.md) | house-rule | Iterate with `lake env lean`, build only your own module |
| [0006](entries/0006-docstring-contract.md) | house-rule | The module docstring is a contract, and the ledger reads its first 4000 characters |
| [0007](entries/0007-neighbourhoods-not-sequences.md) | pattern | Second countability is almost never needed: argue on neighbourhoods and directed families |
| [0008](entries/0008-opens-inf-membership.md) | pattern | Membership in `V ⊓ W` and transport along `≤` of open sets |
| [0009](entries/0009-subdivision.md) | pattern | The Lebesgue-number step is `exists_subdivision_Icc` |
| [0010](entries/0010-dot-notation-on-unfolded-props.md) | pitfall | `h.foo` fails when the type of `h` unfolds to a `∀` |
| [0011](entries/0011-never-outrun-the-paper.md) | house-rule | A Lean statement narrower than the paper's is never its certificate |
| [0012](entries/0012-model-facts-as-hypotheses.md) | pattern | The singular part's model facts are named hypotheses, witnessed on a line |
| [0013](entries/0013-measures-on-open-sets.md) | convention | A measure on an open `U` is a measure on `M` with `μ Uᶜ = 0` |
| [0014](entries/0014-no-gluing-axiom.md) | pitfall | No gluing axiom: a counterexample may exploit it, and must say so |
| [0015](entries/0015-graduation-checklist.md) | house-rule | Graduating a scaffold file: what the gates do not catch by themselves |
| [0016](entries/0016-namespace-shadowing.md) | pitfall | Names that resolve to the wrong lemma inside `namespace Causality` |
| [0017](entries/0017-curves-over-intervals.md) | pattern | Curves over an interval, inextensibility, and the two traps of "maximal under extension" |
| [0018](entries/0018-charts-and-maximal-atlases.md) | pattern | Causalities through charts: transport, `ChartIso`, the maximal atlas |
| [0019](entries/0019-discrete-counterexamples.md) | pitfall | A discrete counterexample is non-local, and says nothing about local causalities |
| [0020](entries/0020-static-spacetimes.md) | pattern | Model spaces are static spacetimes over a geodesic space; cheap local counterexamples |
| [0021](entries/0021-metric-from-a-formula.md) | pattern | A space given by a distance formula with identifications: `SeparationQuotient` |
| [0022](entries/0022-rulings-and-printed-forms.md) | house-rule | After a ruling, the strengthened theorem is principal and the printed form becomes a `Prop` |
| [0023](entries/0023-maximal-chains-of-the-order.md) | pattern | Maximal chains of the causal order, and abstract Section 4 |
| [0024](entries/0024-two-papers-one-library.md) | house-rule | Two papers in one library: Barbot labels are `bthm:`/`bprop:`/…, modules under `Flat/` |
