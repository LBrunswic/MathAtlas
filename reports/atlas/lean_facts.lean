/-!
# The atlas's fact extractor

Not run on its own: `lean_edges.py facts` prepends `import <root>` for each library root of a
package and feeds the result to `lake env lean --stdin` inside that package, so that it reads the
package's built oleans and writes nothing into the package. Two environment variables carry the
parameters: `ATLAS_ROOTS` (comma-separated library roots, e.g. `Causal,CausalScaffold`) and
`ATLAS_OUT` (the absolute path of the JSON to write, under `reports/atlas/lean/`).

For every declaration of every module under those roots it records its kind, module and line and
the project declarations its **type** (`uses_type`, the statement's vocabulary) and its **value**
(`uses_value`, the proof term's) mention, from `Expr.getUsedConstants` -- the schema of
`lean/scripts/lean_facts.lean` (GFNBoundsLean), restricted to what `tools/doubledag.py` reads.

Three differences from that extractor, each so that an edge the proof really has is not lost:

* a constant is *project* when it was declared in a project module, not when its name starts with
  the root: an instance or a private lemma declared in `Causal.Foo` is the project's whatever it
  is called;
* the elaborator's auxiliaries (`_proof_n`, `match_n`, `_auxLemma`, private names, ...) are not
  dropped but **inlined**: what a declaration's `_proof_1` uses, the declaration uses;
* an inductive type's `uses_type` includes its constructors' types, so a structure depends on the
  vocabulary of its fields.

So a step `a → b` of a witness says that `a`'s statement or proof term mentions `b`, directly or
through auxiliaries of `a` that the chain does not name. On the three packages of 2026-11-20 the
three differences add Lean-only edges and change no `both` or `tex-only` edge.
-/

open Lean Meta

namespace AtlasFacts

/-- The elaborator's bookkeeping: the same test as GFNBoundsLean's extractor. -/
def isNoise (n : Name) : Bool :=
  n.isInternalDetail || n.isImplementationDetail ||
    (n.components.any fun c =>
      let s := c.toString
      s.startsWith "_" || s == "proof_1" || s == "eq_def" || s == "match_1")

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- `ConstantInfo.value?` withholds theorem values at this Lean version, so it is written out. -/
def valueOf : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The constants of a declaration's statement: its type, and for an inductive its constructors'. -/
def typeConsts (env : Environment) (ci : ConstantInfo) : Array Name :=
  let base := ci.type.getUsedConstants
  match ci with
  | .inductInfo v => v.ctors.foldl (init := base) fun acc c =>
      match env.find? c with
      | some cc => acc ++ cc.type.getUsedConstants
      | none => acc
  | _ => base

def valueConsts (ci : ConstantInfo) : Array Name :=
  match valueOf ci with
  | some v => v.getUsedConstants
  | none => #[]

/-- The memo of `closeAux`, and the constants whose closure is being computed (cycle guard). -/
structure Refs where
  memo : IO.Ref (Std.HashMap Name (Array Name))
  busy : IO.Ref (Std.HashSet Name)

/-- The non-auxiliary project constants an auxiliary constant `c` reaches through auxiliaries only,
deduplicated (an auxiliary DAG is not unfolded into a tree). -/
partial def closeAux (env : Environment) (proj : Std.HashSet Name) (R : Refs) (c : Name) :
    IO (Array Name) := do
  if let some r := (← R.memo.get)[c]? then return r
  if (← R.busy.get).contains c then return #[]
  R.busy.modify (·.insert c)
  let mut acc : Std.HashSet Name := {}
  if let some ci := env.find? c then
    for k in typeConsts env ci ++ valueConsts ci do
      if k != c && proj.contains k then
        if isNoise k then
          for x in (← closeAux env proj R k) do acc := acc.insert x
        else acc := acc.insert k
  let arr := acc.toArray
  R.memo.modify (·.insert c arr)
  R.busy.modify (·.erase c)
  return arr

/-- Resolve a constant list to project, non-auxiliary names, sorted: auxiliaries are inlined. -/
def resolve (env : Environment) (proj : Std.HashSet Name) (R : Refs) (self : Name)
    (ks : Array Name) : IO (Array String) := do
  let mut acc : Std.HashSet Name := {}
  for k in ks do
    if k != self && proj.contains k then
      if isNoise k then
        for x in (← closeAux env proj R k) do acc := acc.insert x
      else acc := acc.insert k
  let strs := ((acc.erase self).toArray.map (·.toString))
  return strs.qsort (· < ·)

end AtlasFacts

open AtlasFacts in
#eval show MetaM Unit from do
  let env ← getEnv
  let rootsStr := (← IO.getEnv "ATLAS_ROOTS").getD ""
  let out ← match ← IO.getEnv "ATLAS_OUT" with
    | some o => pure o
    | none => throwError "ATLAS_OUT is not set"
  let roots : List Name := (rootsStr.splitOn ",").filter (· ≠ "") |>.map String.toName
  if roots.isEmpty then throwError "ATLAS_ROOTS is empty"
  let isProjMod (m : Name) : Bool := roots.any (·.isPrefixOf m)
  -- Every constant declared in a project module, auxiliaries included.
  let mut proj : Std.HashSet Name := {}
  let mut nmods := 0
  for idx in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    unless isProjMod modName do continue
    nmods := nmods + 1
    for n in env.header.moduleData[idx]!.constNames do
      proj := proj.insert n
  let R : Refs := { memo := ← IO.mkRef {}, busy := ← IO.mkRef {} }
  let t0 ← IO.monoMsNow
  let mut entries : Array (String × Json) := #[]
  for idx in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    unless isProjMod modName do continue
    IO.eprintln s!"{(← IO.monoMsNow) - t0} ms  {modName}"
    for n in env.header.moduleData[idx]!.constNames do
      if isNoise n then continue
      let some ci := env.find? n | continue
      let line : Nat ← do
        match ← findDeclarationRanges? n with
        | some r => pure r.range.pos.line
        | none => pure 0
      let ut ← resolve env proj R n (typeConsts env ci)
      let uv ← resolve env proj R n (valueConsts ci)
      entries := entries.push (n.toString, Json.mkObj [
        ("kind", Json.str (kindOf ci)),
        ("module", Json.str modName.toString),
        ("line", Json.num line),
        ("uses_type", Json.arr (ut.map Json.str)),
        ("uses_value", Json.arr (uv.map Json.str))])
  let outJ := Json.mkObj [
    ("roots", Json.arr ((roots.map (·.toString)).toArray.map Json.str)),
    ("modules", Json.num nmods),
    ("declarations", Json.mkObj entries.toList)]
  IO.FS.writeFile out (outJ.compress ++ "\n")
  IO.println s!"atlas facts: {entries.size} declarations from {nmods} modules of {rootsStr} → {out}"
