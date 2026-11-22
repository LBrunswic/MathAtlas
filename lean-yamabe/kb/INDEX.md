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
| [0009](entries/0009-toy-gluing-input.md) | pattern | A GluingInput with β = c_N on the two-point toy model, once R_g is negative enough |
| [0010](entries/0010-toy-exact-norms.md) | pattern | Exact norms on the two-point toy model, enough for lem:positivity and lem:kobayashi (b) |
| [0011](entries/0011-closed-model-n-zero.md) | pattern | A MeasuredModel with n = 0 is a cheap closed Σ: test whether a statement needs ∂Σ ≠ ∅ |
| [0012](entries/0012-integral-fintype.md) | pitfall | Pitfall: integral_fintype's only explicit argument at this pin is the integrability |
| [0013](entries/0013-the-manifold-layer-yamabe-mfd-mathlib-ma.md) | pattern | The manifold layer Yamabe.Mfd: Mathlib manifolds with boundary, a Riemannian bundle metric, measures read chartwise |
| [0014](entries/0014-6-s-analytic-inputs-on-the-model-sobolev.md) | pattern | § 6's analytic inputs on the model: SobolevIneq, TraceIneq, RellichProp, ConstLimit; lem:positivity from them |
| [0015](entries/0015-riemannianbundle-on-tangentspace-inner-p.md) | pitfall | RiemannianBundle on TangentSpace: inner product by rfl, FiniteDimensional by inferInstanceAs, mfderiv's codomain |
| [0016](entries/0016-under-open-scoped-contdiff-is-ambiguous.md) | pitfall | Under open scoped ContDiff, ∞ is ambiguous; defs not mentioning N need `variable (N) in` |
| [0017](entries/0017-hasderivat-pow-is-the-pi-power-for-fun-t.md) | pitfall | HasDerivAt.pow is the Pi power; for fun t => f t ^ 2 use fun_pow and congr_deriv |
| [0018](entries/0018-free-curvature-data-state-an-external-at.md) | pattern | Free curvature data: state an external at the data where the paper invokes it, not over all metrics |
| [0019](entries/0019-typecheck-a-chain-of-new-scaffold-module.md) | pattern | Typecheck a chain of new scaffold modules through /tmp oleans, without lake build |
