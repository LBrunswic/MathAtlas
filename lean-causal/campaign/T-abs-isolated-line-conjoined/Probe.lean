import CausalScaffold.IsolatedLineConjoined

/-! Probe for T-abs-isolated-line-conjoined (2026-11-27): `#check` and `#print axioms` of every
declaration of `CausalScaffold.IsolatedLineConjoined`; the output is `axioms.txt`. Also a check that
the main declaration carries, as conjuncts, each `from` id and the negated `to` of the isolated
line's two `[[fails]]` entries (`programme/ladder.toml:1805–1809`, `:2029–2033`, as read at 2026-11-27 18:30 UTC). Not built by lake. -/

open Causal

#check @isolatedLine_causallyCompact
#check @isolatedLine_isCausal
#check @isolatedLine_globallyHyperbolic
#check @isolatedLine_hasTimeFunction
#check @isolatedLine_separates

#print axioms isolatedLine_causallyCompact
#print axioms isolatedLine_isCausal
#print axioms isolatedLine_globallyHyperbolic
#print axioms isolatedLine_hasTimeFunction
#print axioms isolatedLine_separates

-- the entry `→ tarentin` (from causally_arc_connected, causally_plain, strongly_causal,
-- strongly_causal_open, causally_open), read off the one witness
example : isolatedLine.CausallyArcConnected ∧ isolatedLine.CausallyPlain ∧
    isolatedLine.StronglyCausal ∧ isolatedLine.StronglyCausalOpen ∧ isolatedLine.CausallyOpen ∧
    ¬ isolatedLine.Tarentin :=
  let ⟨hAC, hCO, hCP, hSC, hSCO, _, _, _, _, _, _, _, _, _, _, _, _, hNT, _, _⟩ :=
    isolatedLine_separates
  ⟨hAC, hCP, hSC, hSCO, hCO, hNT⟩

-- the entry `→ has_chronal_neighbour` (from causally_arc_connected, causally_open, causally_plain,
-- strongly_causal, strongly_causal_open)
example : isolatedLine.CausallyArcConnected ∧ isolatedLine.CausallyOpen ∧
    isolatedLine.CausallyPlain ∧ isolatedLine.StronglyCausal ∧ isolatedLine.StronglyCausalOpen ∧
    ¬ isolatedLine.HasChronalNeighbourEverywhere :=
  let ⟨hAC, hCO, hCP, hSC, hSCO, _, _, _, _, _, _, _, _, _, _, _, _, _, hNH, _⟩ :=
    isolatedLine_separates
  ⟨hAC, hCO, hCP, hSC, hSCO, hNH⟩

-- the conjoined witness subsumes the two split ones it replaces
example : isolatedLine.CausallyArcConnected ∧ isolatedLine.CausallyOpen ∧
    isolatedLine.CausallyPlain ∧ ¬ isolatedLine.HasChronalNeighbourEverywhere ∧
    ¬ isolatedLine.ChronalNeighbours :=
  let ⟨hAC, hCO, hCP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hNH, hNCN⟩ :=
    isolatedLine_separates
  ⟨hAC, hCO, hCP, hNH, hNCN⟩

example : isolatedLine.StronglyCausal ∧ isolatedLine.CausallyOpen ∧ ¬ isolatedLine.Tarentin ∧
    isolatedLine.StronglyCausalOpen :=
  let ⟨_, hCO, _, hSC, hSCO, _, _, _, _, _, _, _, _, _, _, _, _, hNT, _, _⟩ :=
    isolatedLine_separates
  ⟨hSC, hCO, hNT, hSCO⟩
