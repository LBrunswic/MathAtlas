import Causal
import CausalScaffold

/-!
The after-dump of T-abs-dependence-domain-home (kb/0063, extended for a rename): every constant of
every `Causal.*`/`CausalScaffold.*` module, with the columns of `Dump.lean` (T-tac-curves-fact-rule)
and three more: the constant's name with the renamed prefixes mapped back to the old ones, and the
hashes of its type and value after the same substitution inside the terms ("substituting the names
back", kb/0063, kb/0066). `dump_subst_cmp.py` compares those columns with the before-dump.
-/

open Lean Meta

/-- new name → old name (DEC-198). A name below a renamed one (`.eq_1`, …) maps by its prefix. -/
def renames : List (Name × Name) :=
  [(`Causal.Causality.dependenceDomain, `Causal.Flat.dependenceDomain),
   (`Causal.Causality.mem_dependenceDomain, `Causal.Flat.mem_dependenceDomain),
   (`Causal.Causality.dependenceDomain_subset, `Causal.Flat.dependenceDomain_subset),
   (`Causal.Causality.subset_dependenceDomain, `Causal.Flat.subset_dependenceDomain),
   (`Causal.Causality.dependenceDomain_eq_of_isCauchySurfaceOn,
    `Causal.Flat.dependenceDomain_eq_of_isCauchySurfaceOn)]

def oldName (n : Name) : Name := Id.run do
  for (new, old) in renames do
    if new.isPrefixOf n then
      return n.replacePrefix new old
  return n

def substBack (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n ls => let n' := oldName n; if n' != n then some (.const n' ls) else none
    | _ => none

/-- The binder telescope of a type: names with macro scopes erased, binder infos. -/
partial def telescope (e : Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .forallE n _ b bi =>
    let tag := match bi with
      | .default => "()" | .implicit => "{}" | .strictImplicit => "⦃⦄" | .instImplicit => "[]"
    telescope b (acc.push s!"{n.eraseMacroScopes}{tag}")
  | .mdata _ b => telescope b acc
  | _ => acc

#eval show CoreM Unit from do
  let env ← getEnv
  let out ← IO.getEnv "DUMP_OUT"
  let path := out.getD "/tmp/tadd/after-subst.txt"
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  let mut n := 0
  for (name, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`Causal).isPrefixOf modName || (`CausalScaffold).isPrefixOf modName do continue
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    let red := match getReducibilityStatusCore env name with
      | .reducible => "reducible" | .semireducible => "semi" | .irreducible => "irred"
      | _ => "other"
    let value? : Option Expr := match ci with
      | .defnInfo d => some d.value
      | .thmInfo d => some d.value
      | .opaqueInfo d => some d.value
      | _ => none
    let vhash := match value? with | some v => toString v.hash | none => "-"
    let svhash := match value? with | some v => toString (substBack v).hash | none => "-"
    let tel := String.intercalate "," (telescope ci.type).toList
    let prot := if isProtected env name then "prot" else "-"
    let nc := if isNoncomputable env name then "nc" else "-"
    let dep := if Lean.Linter.isDeprecated env name then "deprecated" else "-"
    h.putStrLn s!"{name}\t{modName}\t{kind}\t{ci.levelParams}\t{ci.type.hash}\t{tel}\t{vhash}\t{red}\t{prot}\t{nc}\t{name.isInternal}\t{oldName name}\t{(substBack ci.type).hash}\t{svhash}\t{dep}"
    n := n + 1
  IO.println s!"dumped {n} constants to {path}"
