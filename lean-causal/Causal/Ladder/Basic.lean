import Aesop

/-!
# The `causal_ladder` tactic: the rule set `CausalLadder` and the tactic

The causality ladder of ETT (`programme/ladder.toml`) is a DAG of causal-topological properties
(causal, strongly causal, globally hyperbolic, push-up, causally open, …) whose implications carry
Lean witnesses. This file declares the aesop rule set `CausalLadder` and the tactic
`causal_ladder` that runs aesop on it. The rules themselves are the attributes of the
**generated** module `Causal.Ladder.Rules` (`python3 tools/ladder.py emit-lean`, never edited by
hand), one per `checked` implication of the ladder that carries no side condition (`under`) and
whose witness lives in the ETT layer, and one per `checked` fact (a property every causality has,
on the spaces of its standing) whose witness's module `Causal.Ladder.Rules` may import;
`Causal.Ladder.Test`, generated with it, shows the tactic derives exactly the transitive closure
of the emitted rules. `Causal.Ladder.Rules` imports `Causal.Ladder.Dual`, the hand-written rules
of the same rule set that cross time reversal (`C.dual`), so every user of the tactic has them;
`Causal.Ladder.DualTest` shows what they derive. A rule set must be declared in a module other
than the ones that add rules to it (an aesop restriction), hence this file.

Usage: with hypotheses `hT : C.Tarentin`, `hO : C.CausallyOpen`, `hS : C.StronglyCausal` in
context, `causal_ladder` closes `C.StronglyCausalOpen` or `C.CausallyOpenFuture`. Import
`Causal.Ladder.Rules`, not this file, to have the rules.

## How it searches

Every implication is an aesop **safe forward** rule: an implication `P₁ C → … → Pₙ C → Q C` adds
`Q C` to the context once every `Pᵢ C` is there. A fact `∀ C, P C` is a **safe apply** rule, which
closes a goal `P t` for any causality term `t`, and also a safe forward rule (with the rule
pattern of its causality, so on every causality term in sight) when an implication reads it.
The tactic saturates the context with the consequences of its hypotheses, then closes the goal
by `assumption` (aesop's builtin rules, which also split a conjunction in the goal). Forward
rules suit the ladder: a conjunction premise is matched as it stands, a cycle (strongly causal ⇔
its open form, on a tarentin causally open spacetime) stops because aesop adds no hypothesis
whose type is already present, and a safe rule never commits the search to a branch that cannot
close.

The call is chosen to fail fast: `terminal := true` (it closes the goal or fails, never leaves a
goal behind); the `default` rule set (every global `@[aesop]` rule of mathlib) is disabled, the
builtin set kept; `simp` normalisation is off, so no ladder property is rewritten; the search is
bounded by `maxRuleApplications` (200). The builtin `assumption` still matches up to definitional
equality, so the tactic proves a little more than its rules say (e.g. `C.CausallyArcConnected`
from `C.CausallyArcConnectedOn ⊤`).

Two limits are raised from aesop's defaults (T-tac-ladder-integration). Every forward step is one
rule application along the search's single branch, so `maxRuleApplicationDepth` (aesop's 30)
bounds the saturation itself, and time reversal multiplies it: once `C.dual`, `C.dual.dual`, …
are in sight, every two-sided fact is transported to each of them. At depth 30, from 16 facts of
`C`, the provable `C.dual.dual.dual.CausallyOpenFuture` was not found, and a refuted goal about
`C.dual⁵` (the half-lit line's seven facts) ended at the depth instead of by exhaustive search;
at depth 60 the first closes and the second fails by exhaustion. Termination does not rest on
the depth: no rule writes a time reversal deeper than those in sight (the invariant of
`Causal.Ladder.Dual`'s docstring), and `maxRuleApplications` bounds the work.
`maxSafePrefixRuleApplications` (aesop's 50) bounds only the expansion of the safe prefix that
aesop makes after a failed search, for its error message (`Aesop/Search/ExpandSafePrefix.lean`,
run by `handleNonfatalError` before a terminal failure is thrown); it is raised to 200 with the
depth, as T-tac-ladder-dual's audit proposed, and changes no verdict.

## SCOPE (disclosed)

* The tactic uses hypotheses that are ladder properties of a term, `h : P t`. A hypothesis under a
  binder (`∀ U, P (C.restrict U)`) is not instantiated: the rules are forward, not backward.
* No ladder edge with a side condition becomes a rule (`tools/ladder.py emit-lean` skips every
  edge with a non-empty `under`), so the tactic proves less than the ladder's matrix, which
  chains those edges as if unconditional.
* Separation and countability hypotheses (`[T1Space M]`, `[SecondCountableTopology M]`, the
  ladder's `standing`) are instance arguments: a rule carrying one finds it by instance synthesis,
  and does not fire where synthesis fails. Failing synthesis costs a few milliseconds each time a
  rule is tried, which is why a fact that no implication reads is an apply rule only.
* A fact whose witness's module imports `Causal.Ladder.Rules` cannot be one of its rules (an import
  cycle): `curves_extend` (`Causal.CurvesExtendSecondCountable` imports `Causal.MaximalZorn`, which
  imports `Causal.ErsMughd`, a user of this tactic). `Causal.Ladder.Test` registers its rule
  locally to test it; elsewhere, discharge `C.CurvesExtend` by the witness (kb/0221).
* Nested time reversals in a large context are slow: from 16 facts of `C`, a goal about
  `C.dual⁵` fails at depth 60 after 3.5 s, and one about `C.dual⁷` exceeds the heartbeat budget.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; aesop at the
manifest's revision.
-/

declare_aesop_rule_sets [CausalLadder]

/-- `causal_ladder` proves a property of the causality ladder (`programme/ladder.toml`) from the
ladder properties in the context, by the transitive closure of the ladder's checked implications
without side condition and its facts (the rule set `CausalLadder`, generated in
`Causal.Ladder.Rules`), across time reversal (`Causal.Ladder.Dual`, which `Causal.Ladder.Rules`
imports). It closes the goal or fails; it never leaves a goal behind. -/
macro "causal_ladder" : tactic =>
  `(tactic| aesop (rule_sets := [-default, CausalLadder])
    (config := { terminal := true, enableSimp := false, enableUnfold := false,
                 maxRuleApplications := 200, maxRuleApplicationDepth := 60,
                 maxSafePrefixRuleApplications := 200 }))
