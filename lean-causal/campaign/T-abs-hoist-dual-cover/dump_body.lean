

open Lean Meta

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
  let path := out.getD "/tmp/hdc/dump.txt"
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
    let vhash := match ci with
      | .defnInfo d => toString d.value.hash
      | .thmInfo d => toString d.value.hash
      | .opaqueInfo d => toString d.value.hash
      | _ => "-"
    let tel := String.intercalate "," (telescope ci.type).toList
    let prot := if isProtected env name then "prot" else "-"
    let nc := if isNoncomputable env name then "nc" else "-"
    h.putStrLn s!"{name}\t{modName}\t{kind}\t{ci.levelParams}\t{ci.type.hash}\t{tel}\t{vhash}\t{red}\t{prot}\t{nc}\t{name.isInternal}"
    n := n + 1
  IO.println s!"dumped {n} constants to {path}"
