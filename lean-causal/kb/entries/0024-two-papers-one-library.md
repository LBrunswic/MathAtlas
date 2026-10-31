---
id: 0024
title: Two papers, one library — disjoint label prefixes
kind: house-rule
created: 2026-10-31
---
`lean-causal/` certifies two papers: ETT (`papers/ett`) and Barbot's *Globally hyperbolic flat
space-times* (`papers/barbot`, DEC-34). Both ledgers scan every file under `Causal/` and
`scaffold/CausalScaffold/`, and a docstring mark ``**`label`**`` is read by whichever ledger's
`label_prefixes` matches it. So Barbot's labels carry b-prefixed kinds — `bthm:`, `bprop:`,
`blem:`, `bcor:`, `bdef:` — and never `theo:`/`prop:`/…; the regex needs the backtick right
before the prefix, so `bprop:` never matches ETT's `prop:`. Barbot's modules live under
`Causal/Flat/` and `CausalScaffold/Flat/`, namespace `Causal.Flat`. After touching either, rebuild
BOTH ledgers: ETT's must regenerate unchanged unless an ETT label moved.
Barbot writes ℝ^{1,n-1} as `𝐌ⁿ` (n = total dimension); the library's `Minkowski d` has `d`
spatial dimensions, so Barbot's `n` is `d + 1`. Say so in every Flat docstring.
