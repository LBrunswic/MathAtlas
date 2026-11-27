# Universality and Convergence of Generative Flows — the story, written fresh

*Skeleton (2026-11-25, T-gfn-ledger, DEC-210). The words are the author's; each fragment names the
ledger labels it rests on, and nothing here is copied from the legacy draft
(`tools/no_legacy_prose.py`). The draft keeps its own story and ledger in its repository; this
file is the hub's reading of it, to be written by the author.*

## Objective

Generative flow networks trained by a flow-matching loss are universal, and their training
converges at a rate the loss controls; the doubling graph shows where that control fails.

## S-gfnbounds-1 The headline

*(To be written by the author.)* Universality, and the bounds it rests on. Rests on
`theo:universality_L2`, `theo:RL_CV_bound` and `theo:IL_CV_bound_body`.

## S-gfnbounds-2 The doubling graph

*(To be written by the author.)* The certified counterexample. Rests on `theo:doubling_main` and
`theo:lean_main`.

## Dependency sketch

*(To be drawn once the fragments exist.)* `tools/ledger.py -c papers/gfnbounds/ledger/ledger.toml order`
lists the 131 ledger statements dependencies-first.
