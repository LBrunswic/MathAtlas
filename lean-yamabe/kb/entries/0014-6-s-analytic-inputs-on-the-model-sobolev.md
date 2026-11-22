---
id: 0014
title: § 6's analytic inputs on the model: SobolevIneq, TraceIneq, RellichProp, ConstLimit; lem:positivity from them
kind: pattern
created: 2026-11-22
---
Found by T-yamabe-analysis. The analytic inputs of § 6 on the model are four Props: SobolevIneq, TraceIneq (into L^{p♯}(B_j)), RellichProp, ConstLimit (energy-free L² limits are constant: the connectedness). MeasuredModel.lem_positivity proves lem:positivity from them, sorry-free; all four hold on the strict toyModel (toy_sobolevIneq, toy_traceIneq, toy_rellichProp, toy_constLimit) and ConstLimit fails on toyCut.

Since T-yamabe-integrate-r2: ConstLimit asks MemLp f 2 (an L² limit), without which it is false (kb 0023).
