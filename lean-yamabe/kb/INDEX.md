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
| [0020](entries/0020-fderivwithin-on-chart-functions-a-clm-ca.md) | pitfall | fderivWithin on chart functions: a CLM carrying TangentSpace instances fails ContinuousAdd |
| [0021](entries/0021-u-g-against-the-chart-derivative-mfd-cha.md) | pattern | |∇u|_g against the chart derivative (Mfd.chart_comparison): give IsContinuousRiemannianBundle explicitly |
| [0022](entries/0022-mfd-goodchart-and-mfd-assemble-from-loca.md) | pattern | Mfd.GoodChart and Mfd.assemble: from local chart estimates to global ones by a finite partition of unity |
| [0023](entries/0023-elpnorm-of-a-non-measurable-function-is.md) | pitfall | eLpNorm of a non-measurable function is an inner integral: an L² limit must be AEStronglyMeasurable |
| [0024](entries/0024-parenthesise-iterated-lintegrals-and-att.md) | pitfall | Parenthesise iterated lintegrals: + and ∂μ attach to the inner integral |
| [0025](entries/0025-a-primed-copy-of-a-theorem-checked-ident.md) | pattern | A primed copy of a theorem checked identical by type_of% … = type_of% … := rfl (one universe per Type*) |
| [0026](entries/0026-the-c-reflection-across-z-0-3v-r-4v-r-co.md) | pattern | The C¹ reflection across {z₀ = 0}: −3v∘R₁ + 4v∘R₂, ContDiff by HasFDerivWithinAt.union |
| [0027](entries/0027-typechecking-new-modules-through-tmp-ole.md) | pattern | Typechecking new modules through /tmp oleans: symlink the existing scaffold oleans into /tmp (refines 0019) |
| [0028](entries/0028-pattern.md) | pattern | Pattern: |
| [0029](entries/0029-pitfall.md) | pitfall | Pitfall: |
| [0030](entries/0030-pitfall.md) | pitfall | Pitfall: |
| [0031](entries/0031-pattern.md) | pattern | Pattern: |
| [0032](entries/0032-pattern.md) | pattern | pattern: |
| [0033](entries/0033-pattern.md) | pattern | pattern: |
| [0034](entries/0034-pattern.md) | pattern | pattern: |
| [0035](entries/0035-pitfall.md) | pitfall | pitfall: |
| [0036](entries/0036-pattern.md) | pattern | pattern: |
| [0037](entries/0037-pattern.md) | pattern | Pattern: |
| [0038](entries/0038-pattern.md) | pattern | Pattern: |
| [0039](entries/0039-pattern.md) | pattern | Pattern: |
| [0040](entries/0040-pattern.md) | pattern | Pattern: |
| [0041](entries/0041-pitfall.md) | pitfall | Pitfall: |
| [0042](entries/0042-pitfall.md) | pitfall | Pitfall: |
| [0043](entries/0043-convention.md) | pattern | Convention: |
| [0044](entries/0044-pattern.md) | pattern | pattern: |
| [0045](entries/0045-pattern.md) | pattern | pattern: |
| [0046](entries/0046-pattern.md) | pattern | pattern: |
| [0047](entries/0047-pitfall.md) | pitfall | pitfall: |
| [0048](entries/0048-pitfall.md) | pitfall | pitfall: |
| [0049](entries/0049-pitfall.md) | pitfall | pitfall: |
| [0050](entries/0050-pattern.md) | pattern | pattern: |
| [0051](entries/0051-pattern.md) | pattern | pattern: |
| [0052](entries/0052-pattern.md) | pattern | pattern: |
| [0053](entries/0053-pitfall.md) | pitfall | pitfall: |
| [0054](entries/0054-pattern.md) | pattern | pattern: |
| [0055](entries/0055-pattern.md) | pattern | pattern: |
