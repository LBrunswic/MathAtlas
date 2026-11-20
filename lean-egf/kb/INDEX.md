# Knowledge base — working in `lean-egf`

What working in this library is like: conventions, patterns, pitfalls. Read before you start;
propose an entry when you finish, if you learned something the next session would otherwise
rediscover. One fact per entry. `lean-causal/kb/INDEX.md` holds the hub's older entries (the
docstring contract is its `0006`; weakest hypotheses `0007`; no quiet weakening `0011`).

| id | kind | entry |
|---|---|---|
| [0001](entries/0001-wave-0.md) | convention | Wave 0: Mathlib only; GFNBoundsLean is a template, not a dependency, until a ruling |
| [0002](entries/0002-tv-calculus.md) | pattern | Defects of a generative flow are truncated differences of finite measures; the TV calculus needs no SignedMeasure |
| [0003](entries/0003-truncation.md) | pattern | From L²(λ̂) decay of densities to TV decay without comparing λ and λ̂: truncate first |
| [0004](entries/0004-abel-truncated-difference.md) | pitfall | `abel` fails on measure expressions containing a truncated difference |
| [0005](entries/0005-tendsto-trans-eq.md) | pitfall | `h.trans_eq` on a Tendsto resolves to LE.le.trans_eq |
| [0006](entries/0006-lambda-names.md) | convention | Names: `lam` is λ, `lamHat` is λ̂, `pushIter π n μ` is μπⁿ |
