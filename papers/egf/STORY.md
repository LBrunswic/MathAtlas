# EGF — the story, written fresh

*Skeleton (2026-09-19). The words are the author's; each fragment below names the ledger labels
it rests on, and nothing here is copied from the legacy draft (`tools/no_legacy_prose.py`).*

## Objective

Sample from an unnormalised target on a manifold with a generative flow whose forward policy is
a finite family of globally defined diffeomorphisms, so that the flow-matching loss is tractable
and universality comes from ergodicity rather than from acyclicity.

## S-egf-1 Ergodicity buys universality

The forward policy is a Markov kernel built from finitely many diffeomorphisms; if it is ergodic
with summable L²-mixing coefficients, every pair of L² initial and terminal laws is reachable
up to any ε. Rests on `def:egf`, `def:universal_family`, `def:summably_mixing`,
`theo:universality_true` (body form `theo:universality`). Lean anchor: `EGF.main_universality`.

## S-egf-2 Two concrete universal families

Affine toroidal families and algebraic spherical isometry families are universal, by the
spectral-gap theorems of the literature. Rests on `theo:universality_tori`,
`theo:universality_sphere`, `theo:spectral_gap_tori`, `theo:spectral_gap_sphere` (cited).

## S-egf-3 The sampling error is controlled by the losses

The quantitative sampling theorem bounds the total-variation error of the terminal law by the
initial and terminal defects, and Pinsker turns the KL-weak-FM loss into such a bound. Rests on
`theo:sampling_theorem`, `theo:negative_control`, `theo:negative_control_appendix`,
`cor:sampling_error_control`, `cor:pinsker_negative_control`. Lean anchor:
`EGF.main_quantitative_sampling`.

## S-egf-4 The backward policy is explicit

For a finite family of diffeomorphisms the backward star policy has a closed form, which is what
makes the loss computable. Rests on `theo:backward_policy`.

## Dependency sketch

S-egf-1 → S-egf-2 (the general theorem instantiated); S-egf-1, S-egf-4 → S-egf-3 (the error
bound needs the explicit inflow).
