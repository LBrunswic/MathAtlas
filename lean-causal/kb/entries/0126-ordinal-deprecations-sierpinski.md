---
id: 0126
title: Ordinal deprecations, Sierpiński space and T0Space Prop at this pin
kind: pitfall
created: 2026-11-21
---
At Mathlib fabf563a, Ordinal.isOpen_singleton_iff is deprecated for SuccOrder.isOpen_singleton_iff, and Ordinal.add_one_eq_succ for Order.succ_eq_add_one, with the sides reversed (succ x = x + 1). Sierpiński space is Prop (sierpinskiSpace, continuous_Prop, nhds_true, nhds_false); T0Space Prop IS found by instance search once Mathlib.Topology.Order.LowerUpperTopology is imported (IsUpper Prop, then IsUpper.t0Space), so Causal.t0Space_prop only covers a narrower import set. SecondCountableTopology ℕ needs Mathlib.Topology.Instances.Discrete. (T-abs-omega-one-constant)
