import Aesop

/-!
# The `causal_ladder` tactic: the rule set `CausalLadder` and the tactic

The causality ladder of ETT (`programme/ladder.toml`) is a DAG of causal-topological properties
(causal, strongly causal, globally hyperbolic, push-up, causally open, …) whose implications carry
Lean witnesses. This file declares the aesop rule set `CausalLadder` and the tactic
`causal_ladder` that runs aesop on it. The rules themselves are the attributes of the
**generated** module `Causal.Ladder.Rules` (`python3 tools/ladder.py emit-lean`, never edited by
hand), one per `checked` implication of the ladder that carries no side condition (`under`) and
whose witness lives in the ETT layer; `Causal.Ladder.Test`, generated with it, shows the tactic
derives exactly the transitive closure of the emitted implications. A rule set must be declared
in a module other than the ones that add rules to it (an aesop restriction), hence this file.

Usage: with hypotheses `hT : C.Tarentin`, `hO : C.CausallyOpen`, `hS : C.StronglyCausal` in
context, `causal_ladder` closes `C.StronglyCausalOpen` or `C.CausallyOpenFuture`. Import
`Causal.Ladder.Rules`, not this file, to have the rules.

## How it searches

Every rule is an aesop **safe forward** rule: an implication `P₁ C → … → Pₙ C → Q C` adds
`Q C` to the context once every `Pᵢ C` is there. The tactic saturates the context with the
consequences of its hypotheses, then closes the goal by `assumption` (aesop's builtin rules, which
also split a conjunction in the goal). Forward rules suit the ladder: a conjunction premise is
matched as it stands, a cycle (strongly causal ⇔ its open form, on a tarentin causally open
spacetime) stops because aesop adds no hypothesis whose type is already present, and a safe rule
never commits the search to a branch that cannot close.

The call is chosen to fail fast: `terminal := true` (it closes the goal or fails, never leaves a
goal behind); the `default` rule set (every global `@[aesop]` rule of mathlib) is disabled, the
builtin set kept; `simp` normalisation is off, so no ladder property is rewritten; the search is
bounded by `maxRuleApplications`. The builtin `assumption` still matches up to definitional
equality, so the tactic proves a little more than its rules say (e.g. `C.CausallyArcConnected`
from `C.CausallyArcConnectedOn ⊤`).

## SCOPE (disclosed)

* The tactic uses hypotheses that are ladder properties of a term, `h : P t`. A hypothesis under a
  binder (`∀ U, P (C.restrict U)`) is not instantiated: the rules are forward, not backward.
* No ladder edge with a side condition becomes a rule (`tools/ladder.py emit-lean` skips every
  edge with a non-empty `under`), so the tactic proves less than the ladder's matrix, which
  chains those edges as if unconditional.
* Separation hypotheses (`[T1Space M]`, `[T2Space M]`) are instance arguments: a rule carrying one
  would find it by instance synthesis. None is emitted today (each sits in an `under`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; aesop at the
manifest's revision.
-/

declare_aesop_rule_sets [CausalLadder]

/-- `causal_ladder` proves a property of the causality ladder (`programme/ladder.toml`) from the
ladder properties in the context, by the transitive closure of the ladder's unconditional checked
implications (the rule set `CausalLadder`, generated in `Causal.Ladder.Rules`). It closes the goal
or fails; it never leaves a goal behind. -/
macro "causal_ladder" : tactic =>
  `(tactic| aesop (rule_sets := [-default, CausalLadder])
    (config := { terminal := true, enableSimp := false, enableUnfold := false,
                 maxRuleApplications := 200 }))
