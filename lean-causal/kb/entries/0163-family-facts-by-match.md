---
id: 0163
title: Family-indexed model facts: pattern-match on o, and read Sing through a membership lemma
kind: pitfall
created: 2026-11-21
---
Write family facts as `| none => E0LM.e0_locZplus | some κ => @massive_locZplus κ.1 ⟨κ.2⟩`. To read `Sing (MassAModel none)` as the axis, go through a membership lemma stated under the local instance `E0GX.singularGX` (`SFALocal.mem_sing_e0_iff`) and apply it by `exact`: `rw [E0GX.sing_eq]` at a family-instance occurrence may not match, the instance terms differing syntactically. Likewise `massive_mem_sing` for `E_κ` (from `EAlphaGX.reg_sing_cases`) (T-ett-sfa-local).
