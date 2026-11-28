import GFNBounds.Paper.Attribute

/-!
# Tests of the paper attribute and of the conjunct derivation

The tests of section 8 of LeanLink's `docs/design/PAPER-ATTRIBUTE.md`, run inside
`lake build GFNBounds` on every `make check`: a regression is a build error. Every test label has
the form `lem:paperattr_test_*` (or `thm:paperattr_test_*` for the bad prefix), which no paper
source contains.

Nothing persists and nothing exports. A placement that must succeed, and every declaration a
fixture needs, is elaborated inside `withoutModifyingEnv`, so its entries vanish with the restored
environment and no declaration of this module reaches `docs/lean-facts.json`. The module's own
declarations are a `private` theorem and two `private` helper defs (all skipped by `isNoise`). Every expected message is written for
the namespace `GFNBounds.Paper.Test`, relative to which `MessageData.ofConstName` prints.

Provenance: Lean core only (toolchain `v4.31.0`); no Mathlib import.
-/

open Lean Elab Command Meta

namespace GFNBounds.Paper.Test

/-! ## Negative: each placement is refused with its exact message -/

/-- error: paper: malformed label 'Lemma 3' -/
#guard_msgs in
attribute [paper "Lemma 3"] GFNBounds.Paper.validLabel

/-- error: paper: malformed label 'thm:paperattr_test_prefix' -/
#guard_msgs in
attribute [paper "thm:paperattr_test_prefix"] GFNBounds.Paper.validLabel

/-- error: paper: malformed label 'lem:paperattr_test_zero.0' -/
#guard_msgs in
attribute [paper "lem:paperattr_test_zero.0"] GFNBounds.Paper.validLabel

/-- error: paper: a placement must be global, not scoped or local -/
#guard_msgs in
attribute [local paper "lem:paperattr_test_local"] GFNBounds.Paper.validLabel

/-- error: paper: Nat.add_comm is outside GFNBounds, private or internal -/
#guard_msgs in
attribute [paper "lem:paperattr_test_ns"] Nat.add_comm

private theorem privTrue : True := trivial

/-- error: paper: privTrue is outside GFNBounds, private or internal -/
#guard_msgs in
attribute [paper "lem:paperattr_test_private"] privTrue

/-- error: paper: label 'lem:paperattr_test_dup' is already the statement of validLabel -/
#guard_msgs in
run_cmd withoutModifyingEnv do
  elabCommand (← `(attribute [paper "lem:paperattr_test_dup"] GFNBounds.Paper.validLabel))
  elabCommand (← `(attribute [paper "lem:paperattr_test_dup"] GFNBounds.Paper.labels))

/-! ## Positive: placement, item label, repeated placement, query -/

#guard_msgs in
run_cmd withoutModifyingEnv do
  elabCommand (← `(attribute [paper "lem:paperattr_test_pos"] GFNBounds.Paper.validLabel))
  elabCommand (← `(attribute [paper "lem:paperattr_test_pos.2"] GFNBounds.Paper.validLabel))
  elabCommand (← `(attribute [paper "lem:paperattr_test_pos"] GFNBounds.Paper.validLabel))
  let got := labels (← getEnv)
  let want : Array (String × Name) :=
    #[("lem:paperattr_test_pos", `GFNBounds.Paper.validLabel),
      ("lem:paperattr_test_pos.2", `GFNBounds.Paper.validLabel)]
  unless got == want do
    throwError "paper test: labels returned {repr got}, expected {repr want}"

/-! ## Nothing persists: the placements above vanished with their environment -/

#guard_msgs in
run_cmd do
  let got := labels (← getEnv)
  unless got.isEmpty do
    throwError "paper test: {got.size} placement(s) survived withoutModifyingEnv"

/-! ## Conjuncts: the clean shapes -/

/-- Run `conjunctsOf` on `decl` and fail unless it returns `want`. -/
private def expectConjuncts (decl : Name) (want : Array Name) : CommandElabM Unit := do
  let got ← liftTermElabM (conjunctsOf decl)
  unless got == want do
    throwError "paper test: conjunctsOf {decl} returned {got}, expected {want}"

/-- Run `conjunctsOf` on `decl` and fail unless it throws exactly the message `msg`. -/
private def expectConjunctsFail (decl : Name) (msg : String) : CommandElabM Unit := do
  let r ← liftTermElabM do
    try
      let got ← conjunctsOf decl
      return Sum.inl got
    catch e => return Sum.inr (← e.toMessageData.toString)
  match r with
  | .inl got => throwError "paper test: conjunctsOf {decl} returned {got}, expected a failure"
  | .inr m =>
    unless m == msg do
      throwError "paper test: conjunctsOf {decl} failed with '{m}', expected '{msg}'"

set_option hygiene false in
#guard_msgs in
run_cmd withoutModifyingEnv do
  elabCommand (← `(theorem hderive (n : Nat) (h : 0 < n) : 0 < n + 0 := h))
  elabCommand (← `(theorem a (n : Nat) (_h : 0 < n + 0) : n = n := rfl))
  elabCommand (← `(theorem b : 0 = 0 := rfl))
  elabCommand (← `(theorem c : 1 = 1 := rfl))
  elabCommand (← `(theorem ab (n : Nat) (_h : 0 < n) : n = n ∧ 0 = 0 := ⟨rfl, rfl⟩))
  elabCommand (← `(theorem qimp {n : Nat} : n + 0 = n := rfl))
  -- an anonymous constructor with binders and an instantiated hypothesis
  elabCommand (← `(theorem t1 (n : Nat) (h : 0 < n) : n = n ∧ 0 = 0 ∧ 1 = 1 :=
    ⟨a n (hderive n h), b, c⟩))
  expectConjuncts `GFNBounds.Paper.Test.t1
    #[`GFNBounds.Paper.Test.a, `GFNBounds.Paper.Test.b, `GFNBounds.Paper.Test.c]
  -- projections
  elabCommand (← `(theorem t2 (n : Nat) (h : 0 < n) : 0 = 0 ∧ n = n :=
    ⟨(ab n h).2, (ab n h).1⟩))
  expectConjuncts `GFNBounds.Paper.Test.t2 #[`GFNBounds.Paper.Test.ab]
  -- `refine` then `exact`
  elabCommand (← `(theorem t3 : 0 = 0 ∧ 1 = 1 := by
    refine ⟨?_, c⟩
    exact b))
  expectConjuncts `GFNBounds.Paper.Test.t3 #[`GFNBounds.Paper.Test.b, `GFNBounds.Paper.Test.c]
  -- `have` then a tuple
  elabCommand (← `(theorem t4 (n : Nat) (h : 0 < n) : n = n ∧ 1 = 1 := by
    have h0 := hderive n h
    exact ⟨a n h0, c⟩))
  expectConjuncts `GFNBounds.Paper.Test.t4 #[`GFNBounds.Paper.Test.a, `GFNBounds.Paper.Test.c]
  -- an implicit binder
  elabCommand (← `(theorem t5 : (∀ {n : Nat}, n + 0 = n) ∧ 1 = 1 := ⟨qimp, c⟩))
  expectConjuncts `GFNBounds.Paper.Test.t5
    #[`GFNBounds.Paper.Test.qimp, `GFNBounds.Paper.Test.c]

/-! ## Conjuncts: the glue `conjunctsOf` must refuse -/

set_option hygiene false in
#guard_msgs in
run_cmd withoutModifyingEnv do
  elabCommand (← `(theorem c : 1 = 1 := rfl))
  elabCommand (← `(theorem b : 0 = 0 := rfl))
  elabCommand (← `(theorem lt1 (n : Nat) : n < n + 1 := Nat.lt_succ_self n))
  elabCommand (← `(structure Pair (P Q : Prop) : Prop where
    l : P
    r : Q))
  -- a glue lemma around a conjunct
  elabCommand (← `(theorem f1 (n : Nat) : n ≤ n + 1 ∧ 1 = 1 := ⟨Nat.le_of_lt (lt1 n), c⟩))
  expectConjunctsFail `GFNBounds.Paper.Test.f1
    "paper: conjunctsOf GFNBounds.Paper.Test.f1: the head \
      Nat.le_of_lt of a leaf is not a project theorem"
  -- `absurd`
  elabCommand (← `(theorem f2 (h : ¬ 1 = 1) : 2 = 3 ∧ 1 = 1 := ⟨absurd c h, c⟩))
  expectConjunctsFail `GFNBounds.Paper.Test.f2
    "paper: conjunctsOf GFNBounds.Paper.Test.f2: the head \
      absurd of a leaf is not a project theorem"
  -- existential packaging
  elabCommand (← `(theorem f3 : ∃ n : Nat, 0 < n ∧ 1 = 1 := ⟨1, Nat.one_pos, c⟩))
  expectConjunctsFail `GFNBounds.Paper.Test.f3
    "paper: conjunctsOf GFNBounds.Paper.Test.f3: the head \
      Exists.intro of a leaf is not a project theorem"
  -- a project structure's constructor used as packaging
  elabCommand (← `(theorem f4 : Pair (0 = 0) (1 = 1) ∧ 1 = 1 := ⟨⟨b, c⟩, c⟩))
  expectConjunctsFail `GFNBounds.Paper.Test.f4
    "paper: conjunctsOf GFNBounds.Paper.Test.f4: the head \
      GFNBounds.Paper.Test.Pair.mk of a leaf is not a project theorem"
  -- `cases` on a project structure
  elabCommand (← `(theorem f5 (p : Pair (0 = 0) (1 = 1)) : 0 = 0 ∧ 1 = 1 := by
    cases p with
    | mk l r => exact ⟨l, r⟩))
  expectConjunctsFail `GFNBounds.Paper.Test.f5
    "paper: conjunctsOf GFNBounds.Paper.Test.f5: the head \
      GFNBounds.Paper.Test.Pair.casesOn of a leaf is not a project theorem"
  -- a structure projection
  elabCommand (← `(theorem f6 (p : Pair (0 = 0) (1 = 1)) : 0 = 0 ∧ 1 = 1 := ⟨p.l, c⟩))
  expectConjunctsFail `GFNBounds.Paper.Test.f6
    "paper: conjunctsOf GFNBounds.Paper.Test.f6: the head \
      GFNBounds.Paper.Test.Pair.l of a leaf is not a project theorem"
  -- a `rw` on the goal (beyond the section 8 list; named in its section 10)
  elabCommand (← `(theorem f7 : 0 + 0 = 0 ∧ 1 = 1 := by
    rw [Nat.add_zero]
    exact ⟨b, c⟩))
  expectConjunctsFail `GFNBounds.Paper.Test.f7
    "paper: conjunctsOf GFNBounds.Paper.Test.f7: the head \
      Eq.mpr of a leaf is not a project theorem"

end GFNBounds.Paper.Test
