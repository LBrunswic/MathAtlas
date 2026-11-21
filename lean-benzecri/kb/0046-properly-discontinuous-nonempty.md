# 0046 — Pitfall: ProperlyDiscontinuousSMul's set is .Nonempty at this pin

*Found 2026-11-21 by T-bz-result-b-proj; recorded by the master session.*

At mathlib fabf563a the set in ProperlyDiscontinuousSMul is {γ | ((γ • ·) '' K ∩ L).Nonempty}, not `≠ ∅`: destructure membership as ⟨_, ⟨x, hxK, rfl⟩, hxL⟩.
