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
| [0007](entries/0007-posterior-is-backward-policy.md) | pattern | Mathlib's posterior is the backward policy |
| [0008](entries/0008-change-of-variables-as-measures.md) | pattern | Change of variables on ℝⁿ as an equality of measures |
| [0009](entries/0009-pin-api-and-infty.md) | pitfall | At this pin: lintegral_finsetSum, zero_le, and the ∞ of open scoped ContDiff |
| [0010](entries/0010-cheap-counterexamples-on-r.md) | pattern | Cheap measure counterexamples on ℝ: translations and restricted Lebesgue |
| [0011](entries/0011-ionescu-tulcea-chain.md) | pattern | A homogeneous chain by Ionescu-Tulcea, and a sampler with a randomized stopping time |
| [0012](entries/0012-tv-without-signed-measure.md) | pattern | Total variation without SignedMeasure: tvDist := tvMass/2 |
| [0013](entries/0013-pin-pitfalls-kernel.md) | pitfall | At this pin: Kernel.piecewise needs DecidablePred; mul_le_mul_left multiplies on the right |
| [0014](entries/0014-pinsker-and-kappa-hat.md) | pattern | Pinsker with Mathlib's klDiv: EGF.pinsker; inference at κ̂ |
| [0015](entries/0015-scope-in-8000-and-pitfalls.md) | pitfall | The ledger reads SCOPE from the first 8000 characters; two measure pitfalls |
| [0016](entries/0016-nonsingular-moves-inflow.md) | pattern | F_in ≪ λ for an EGF from nonsingular moves; Haar null sets without the Jacobian |
| [0017](entries/0017-universality-plug-in-bool.md) | pattern | The universality plug-in (IsUniversalPolicy → IsUniversalFamilyEps); cheap counterexamples on Bool |
| [0018](entries/0018-loss-kl-and-reversed-flow.md) | pattern | The KL-weakFM loss: KL between densities, computable KLs on Bool, the reversed flow |
| [0019](entries/0019-universality-from-ergodicity.md) | pattern | Universality from ergodicity alone (Cesàro, von Neumann); necessity with no invariant measure |
| [0020](entries/0020-torus-haar-without-jacobian.md) | pattern | Haar measure on UnitAddTorus without a Jacobian; the global probability instance on UnitAddCircle |
| [0021](entries/0021-group-action-notions.md) | convention | Group-action notions live in EGF.TorusFamilies; IsGroupErgodic is ErgodicSMul without the invariance |
| [0022](entries/0022-family-is-image-of-model.md) | pattern | A paper's parameterized family is the image of a model, never a membership predicate |
| [0023](entries/0023-sphere-toolkit.md) | pattern | Spheres, SO(n), SU(d) and S¹: the toolkit of EGF.SphereFamilies; name instances on matrix groups |
| [0024](entries/0024-mixing-under-invariance.md) | pattern | Mixing under invariance; deterministic kernels are never summably mixing; OQ-47's vacuous reading |
| [0025](entries/0025-pin-pitfalls-families.md) | pitfall | Pitfalls at this pin from the families and mixing targets |
