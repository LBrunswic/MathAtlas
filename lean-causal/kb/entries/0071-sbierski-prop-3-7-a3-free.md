---
id: 0071
title: Sbierski Prop 3.7 (i) ⇒ (ii) without A3; (iii) fails at BTZ points
kind: pattern
created: 2026-11-21
---
`Causal.CBG.sbierski_prop_3_7_i_imp_ii` (`Causal.SbierskiProp37`, ETT-layer, no A3): `KSide` form,
both time orientations, no side of a Cauchy surface; `_ladder` from push-up, GH, tarentin and N
causally arc-connected; the core `IsCorrPair.tendsto_comp_of_chain` works for any chronological
chain. No timelike curve ends at a BTZ point (I⁻ = ∅), so (i) ⇔ (iii) fails there
(`lightlikeLine_sbierski_prop_3_7_iii_fails`); it holds at regular points under causal
arc-connectedness (`sbierski_prop_3_7`). Helpers: `CausallyArcConnected.mem_Zminus_iff` (Z⁻ from
I⁻ ≠ ∅), `Causality.mem_of_le_of_lt_of_mem_closure` (no countability) (T-abs-sbierski-prop-3-7).
