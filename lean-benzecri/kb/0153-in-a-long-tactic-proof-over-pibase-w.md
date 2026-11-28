# 0153 — In a long tactic proof over PiBase with `let`-bound charts, `rw [IsProjIso.toAut_smul,

*Found 2026-11-28 by T-bz-c3-prop4-produit; recorded by the master session.*

In a long tactic proof over PiBase with `let`-bound charts, `rw [IsProjIso.toAut_smul, piTorusAut_mk_smul]` hit the 200000-heartbeat whnf limit; moving that step into a generic lemma with B a variable (isCompatiblePi_of_transport) removed it. Likewise `obtain ⟨k, ⟨b⟩⟩ := …` on a goal mentioning PiBase timed out; `(h).elim fun k hk => hk.elim fun b => ?_` did not. Use `let`, never `set`, for the Opens family (kb 0015), and make a set-valued helper `abbrev` when it appears inside an `Opens` structure the goal compares under instance transparency.
