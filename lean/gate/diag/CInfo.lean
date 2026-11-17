import Lean
/-!
`#cinfo_mods P` prints one line per definition declared in modules whose name starts with `P`:
name, level parameters, reducibility hints, safety and structural hashes of type and value.
`#cinfo n₁ n₂ …` prints the same line for the named constants, then their values with `pp.all`.
Used by `gate/comparator_run.py` to locate a challenge definition that does not match the library.
-/
open Lean Elab Command

def hintStr : ReducibilityHints → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => s!"regular {h}"

def safetyStr : DefinitionSafety → String
  | .unsafe => "unsafe"
  | .safe => "safe"
  | .partial => "partial"

def cinfoLine (n : Name) (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo d => s!"{n}\tdef\t{d.levelParams}\t{hintStr d.hints}\t{safetyStr d.safety}\t{d.type.hash}\t{d.value.hash}"
  | .inductInfo d => s!"{n}\tinductive\t{d.levelParams}\t{d.type.hash}\t{d.ctors}"
  | .ctorInfo d => s!"{n}\tctor\t{d.levelParams}\t{d.type.hash}"
  | .recInfo d => s!"{n}\trec\t{d.levelParams}\t{d.type.hash}"
  | .thmInfo d => s!"{n}\tthm\t{d.levelParams}\t{d.type.hash}"
  | ci => s!"{n}\tother\t{ci.type.hash}"

elab "#cinfo_mods " p:ident : command => do
  let env ← getEnv
  let pre := p.getId
  let mut lines := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if pre.isPrefixOf m && !n.isInternal then
        lines := lines.push (cinfoLine n ci)
  logInfo (String.intercalate "\n" (lines.qsort (· < ·)).toList)

elab "#cinfo " ns:ident* : command => do
  let env ← getEnv
  for id in ns do
    let n := id.getId
    match env.find? n with
    | some ci =>
      logInfo (cinfoLine n ci)
      if let some v := ci.value? then
        let fmt ← liftTermElabM <| withOptions (fun o => (o.setBool `pp.all true)) <| Meta.ppExpr v
        logInfo m!"{n} value:\n{fmt}"
    | none => logInfo m!"{n} missing"

elab "#cinfo_lines " ns:ident* : command => do
  let env ← getEnv
  let lines := ns.map fun id =>
    match env.find? id.getId with
    | some ci => cinfoLine id.getId ci
    | none => s!"{id.getId}\tmissing"
  logInfo (String.intercalate "\n" lines.toList)
