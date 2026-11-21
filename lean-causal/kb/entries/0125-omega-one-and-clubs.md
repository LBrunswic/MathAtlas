---
id: 0125
title: ω₁ and clubs at this Mathlib pin
kind: pattern
created: 2026-11-21
---
ω₁ is the scoped notation Ordinal.omega 1 (open Ordinal). Iio (ω₁ : Ordinal.{u}) carries OrderTopology automatically (the subspace of Ordinal, orderTopology_of_ordConnected); (ω₁).ToType has no topology. Cofinality: Order.cof α for a type, Ordinal.cof for an ordinal; Ordinal.cof_Iio, Ordinal.lift_cof, Cardinal.cof_omega_one (= ℵ₁). IsClub (Mathlib/SetTheory/Cardinal/Cofinality/Club.lean) states closedness as DirSupClosed: from a closed set use IsLUB.mem_of_isClosed, from a limit condition use IsLUB.isSuccLimit_of_notMem. Countable sups below ω₁: Ordinal.iSup_lt_omega_one; ω₁ additively principal: Ordinal.isPrincipal_add_omega 1; countable predecessors: Causal.countable_Iio_of_lt_omega_one. (T-abs-omega-one-constant)
