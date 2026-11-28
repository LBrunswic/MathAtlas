import Lean

/-!
# The paper attribute: a placement links a paper label to its Lean statement

The attribute `@[paper "<label>"]`, written in the central form
`attribute [paper "<label>"] <decl>`, records that the declaration *is* the Lean statement of the
paper label. It is built as specified in LeanLink's
`docs/design/PAPER-ATTRIBUTE.md`, section 3 (`tools/leanlink` in the hub, read-only), adopted by
DEC-201 of the hub.

This module registers, in this order:

1. `paperExt`, a persistent environment extension whose entries are `Entry`s (a label and a
   declaration name). Entries are appended per module and concatenated on import, so a placement
   is stored in the `.olean` of the module that makes it.
2. The syntax `paper "<label>"`.
3. The attribute itself, whose `add` checks, in order, so that each failure has one cause: the
   attribute kind is global; the label is well formed (`validLabel`, section 4 of the spec); the
   declaration is a public project declaration (`isProject` and not `isNoise`); a repeated
   placement is a no-op; a label already recorded for another declaration is refused.
4. The query `labels`, and the conjunct derivation `conjunctsOf` read by the exporter.

The attribute accepts declarations from imported modules, which Lean's parametric attributes
refuse; that is why it is implemented on its own extension rather than as a parametric attribute.

No import-time duplicate check is possible here: the import hook of an environment extension is
pure and cannot throw. Two modules that do not import each other can both place one label; the
exporter is where that case is caught.

The attribute cannot be used in this module (an `initialize` restriction). Its tests are in
`GFNBounds.Paper.AttributeTest`.

The predicates `isProject` and `isNoise` are those of `scripts/lean_facts.lean`, namespace
`LeanFacts`. That file is a script, not a library module, so it cannot be imported here; the two
predicates are reproduced below verbatim.

Provenance: Lean core only (toolchain `v4.31.0`); no Mathlib import.
-/

open Lean Elab Meta

namespace GFNBounds.Paper

/-- One placement: a paper label and the declaration that states it. -/
structure Entry where
  /-- The paper label, as written in the placement. -/
  label : String
  /-- The declaration the label is placed on. -/
  decl : Name
  deriving Inhabited, Repr, BEq

/-- The project namespace. A copy of `LeanFacts.proj` in `scripts/lean_facts.lean`. -/
def proj : Name := `GFNBounds

/-- A project name: one under the `GFNBounds` namespace. A copy of `LeanFacts.isProject` in
`scripts/lean_facts.lean`. -/
def isProject (n : Name) : Bool := proj.isPrefixOf n

/-- Equation lemmas, match auxiliaries, private names and the rest of the elaborator's
bookkeeping. A verbatim copy of `LeanFacts.isNoise` in `scripts/lean_facts.lean`. -/
def isNoise (n : Name) : Bool :=
  n.isInternalDetail || n.isImplementationDetail ||
    (n.components.any fun c =>
      let s := c.toString
      s.startsWith "_" || s == "proof_1" || s == "eq_def" || s == "match_1")

/-- The statement prefixes a label may carry. -/
def labelPrefixes : List String := ["theo", "lem", "prop", "cor", "def", "rem", "assum"]

/-- A character of a label's body: `[A-Za-z0-9_]`. -/
def isLabelBodyChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- An item number: `[1-9][0-9]*`. -/
def isItemNumber (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => c.isDigit && c != '0' && cs.all Char.isDigit

/-- A well-formed label, written by hand for want of a regex library:
`^(theo|lem|prop|cor|def|rem|assum):[A-Za-z0-9_]+(\.[1-9][0-9]*)?$`. -/
def validLabel (l : String) : Bool :=
  match l.splitOn ":" with
  | [pre, rest] =>
    labelPrefixes.contains pre &&
      match rest.splitOn "." with
      | [body] => !body.isEmpty && body.all isLabelBodyChar
      | [body, item] => !body.isEmpty && body.all isLabelBodyChar && isItemNumber item
      | _ => false
  | _ => false

/-- The placements: imported ones in import order, then this module's in placement order. -/
initialize paperExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `GFNBounds.Paper.paperExt
    addEntryFn := Array.push
    addImportedFn := fun as => as.flatten
    asyncMode := .mainOnly }

/-- `paper "<label>"`: the declaration is the Lean statement of the paper label. -/
syntax (name := paper) "paper " str : attr

/-- Every placement visible in `env`, as `(label, declaration)` pairs, in order. -/
def labels (env : Environment) : Array (String × Name) :=
  (paperExt.getState env).map fun e => (e.label, e.decl)

/-- The `add` hook of the attribute, with its checks in the order of the spec. -/
def addPlacement (decl : Name) (stx : Syntax) (kind : AttributeKind) : AttrM Unit := do
  unless kind == AttributeKind.global do
    throwError "paper: a placement must be global, not scoped or local"
  let l ← match stx with
    | `(attr| paper $s:str) => pure s.getString
    | _ => throwError "paper: expected `paper \"<label>\"`"
  unless validLabel l do
    throwError "paper: malformed label '{l}'"
  unless isProject decl && !isNoise decl do
    throwError "paper: {MessageData.ofConstName decl} is outside GFNBounds, private or internal"
  let env ← getEnv
  for e in paperExt.getState env do
    if e.label == l then
      if e.decl == decl then return
      throwError "paper: label '{l}' is already the statement of {MessageData.ofConstName e.decl}"
  modifyEnv fun env => paperExt.addEntry env { label := l, decl := decl }

initialize registerBuiltinAttribute {
    name := `paper
    descr := "the declaration is the Lean statement of the given paper label"
    add := addPlacement
    erase := fun _ => throwError "paper: a placement cannot be erased" }

/-- Strip, at the root of a proof term or of a leaf: metadata, `fun` binders (including the
implicit lambdas elaboration inserts) and `let`/`have` bindings (`have` elaborates to a
non-dependent `letE`). The value of a `let`/`have` is a hypothesis derivation and is dropped. -/
partial def stripBinders : Expr → Expr
  | .mdata _ e => stripBinders e
  | .lam _ _ b _ => stripBinders b
  | .letE _ _ _ b _ => stripBinders b
  | e => e

/-- Look through `And.left`/`And.right` projections at a leaf, stripping as at the root after each
one. -/
partial def throughAndProj (e : Expr) : Expr :=
  let e := stripBinders e
  if e.isAppOfArity ``And.left 3 || e.isAppOfArity ``And.right 3 then
    throughAndProj e.appArg!
  else
    match e with
    | .proj ``And _ s => throughAndProj s
    | _ => e

/-- The leaves of the nested `And.intro` of a proof term, left to right. -/
partial def andLeaves (e : Expr) : Array Expr :=
  let e := stripBinders e
  if e.isAppOfArity ``And.intro 4 then
    andLeaves (e.getArg! 2) ++ andLeaves (e.getArg! 3)
  else
    #[e]

/-- A conjunct head: a project theorem (`isProject` and not `isNoise`) that is not a projection
function, a constructor or a recursor. -/
def isConjunctHead (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.thmInfo _) =>
    isProject c && !isNoise c && !env.isProjectionFn c && !isAuxRecursor env c &&
      !isRecCore env c
  | _ => false

/-- The declarations whose statements the theorem `decl` conjoins, read on its proof term: at the
root and at every leaf, strip metadata, binders and `let`/`have`; split the nested `And.intro`; at
each leaf look through `And.left`/`And.right` and take the head constant. Left to right, a repeated
name once. Fails, naming the declaration and the leaf, when a leaf is not a constant application
or its head is not a project theorem (`isConjunctHead`). -/
def conjunctsOf (decl : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some (.thmInfo v) := env.find? decl
    | throwError "paper: conjunctsOf: {MessageData.ofConstName decl} is not a theorem"
  let mut out : Array Name := #[]
  for leaf in andLeaves v.value do
    let leaf := throughAndProj leaf
    match leaf.getAppFn with
    | .const c _ =>
      unless isConjunctHead env c do
        throwError "paper: conjunctsOf {MessageData.ofConstName decl}: the head \
          {MessageData.ofConstName c} of a leaf is not a project theorem"
      unless out.contains c do out := out.push c
    | _ =>
      throwError "paper: conjunctsOf {MessageData.ofConstName decl}: a leaf is not a constant \
        application: {leaf}"
  return out

end GFNBounds.Paper
