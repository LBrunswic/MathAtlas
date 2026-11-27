# Cauchy-compact flat spacetimes with extreme BTZ — the story, written fresh

*Skeleton (2026-11-27, T-btz-ledger, DEC-208). The words are the author's; each fragment names the
ledger labels it rests on, and nothing here is copied from the legacy draft
(`tools/no_legacy_prose.py`). The paper's Lemmas 2.3–2.18 are already in lean-gx, for E₀-manifolds,
as gx's cited results; whether the paper is formalized for E_{≥0}-manifolds as printed is the
author's question T-btz-scope.*

## Objective

A globally hyperbolic flat spacetime with extreme BTZ lines has a maximal BTZ-extension, unique up to
isomorphism, and Cauchy-completeness and Cauchy-maximality survive the passage to it.

## S-btz-1 The headline

*(To be written by the author.)* Rests on `btzthm:princ_intro`, `btzthm:BTZ_ext` and
`btzthm:BTZ_Cauchy-completness`.

## S-btz-2 Surgery and absolute maximality

*(To be written by the author.)* The spear neighbourhoods and the surgery along them, then absolute
maximality. Rests on `btzlem:tube`, `btzlem:curve_extension` and `btzprop:abs_max`.

## Dependency sketch

*(To be drawn once the fragments exist.)* `tools/ledger.py -c papers/btz/ledger/ledger.toml order`
lists the 55 ledger statements dependencies-first.
