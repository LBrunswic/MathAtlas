---
id: 0154
title: The E≥0 model family's singular structures: massAModelSingularGX, and when it does not fire
kind: pitfall
created: 2026-11-21
---
`Causal.MassAModelsInstance.massAModelSingularGX` is a global instance by cases on `o`, equal by `rfl` to `E0GX.singularGX` at `none` (`massAModelSingularGX_none`, the `h0` of `BPrimeE0.hiso_massAModel_none`) and to `EAlphaGX.singularGXFamily κ` at `some κ`; `hreg_massAModel`. It fires only for a variable `o`: `MassAModel none` / `MassAModel (some κ)` reduce to `E0` / `Massive κ.1` before instance search. At a fixed model use `attribute [local instance] E0GX.singularGX` (or `EAlphaGX.singularGX`), or `letI := massAModelSingularGX (some κ)` inside a proof; a type ascription naming a fixed model fails for the same reason (T-ett-massa-models-instance).
