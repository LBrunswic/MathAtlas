# Knowledge base — working in `lean-yamabe`

What working in this library is like: conventions, patterns, pitfalls. Read before you start;
propose an entry when you finish. One fact per entry. `lean-causal/kb/INDEX.md` holds the hub's
older entries (the docstring contract is its `0006`; weakest hypotheses `0007`; no quiet weakening `0011`).

| id | kind | entry |
|---|---|---|
| [0001](entries/0001-wave-0.md) | convention | Wave 0: Mathlib only |
| [0002](entries/0002-measured-frame-model.md) | pattern | The abstract measured-frame model of (Σ, ⊔B_j), with a two-point witness |
| [0003](entries/0003-matrix-and-lp-pitfalls.md) | pitfall | Positive definite factorisation, squared L^q norms, dominated derivatives at this pin |
| [0004](entries/0004-curved-metric.md) | pattern | Curvature over the frame model: Yamabe.CurvedMetric |
| [0005](entries/0005-real-sinf-nonpositive.md) | pattern | A real infimum with a nonpositive lower bound needs no nonemptiness |
| [0006](entries/0006-integral-sq-and-junk.md) | pattern | ∫ f² as a squared L² norm; absorbing a junk Bochner integral |
| [0007](entries/0007-filling-and-conformal.md) | pattern | Conformal metrics and the filling of Σ by the D_j on the frame model |
| [0008](entries/0008-neg-literal-and-empty-iinf.md) | pitfall | A literal −1 into an implicit real; Real.iInf over an empty type is 0 |
