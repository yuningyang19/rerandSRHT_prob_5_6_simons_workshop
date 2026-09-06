import Lean
import Mathlib.Util.PrintSorries

open Lean Elab Command

namespace Problem56.PaperV6

private def valueConstants (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo v => v.value.getUsedConstants
  | .thmInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | .inductInfo v => v.ctors.toArray
  | .recInfo v => v.rules.foldl (fun acc r => acc ++ #[r.ctor] ++ r.rhs.getUsedConstants)
      v.all.toArray
  | _ => #[]

private def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

private def names (ns : Array Name) : Json :=
  toJson ((ns.qsort Name.lt).map Name.toString)

/-- Every namespace is traversed. This does not use cached collectAxioms metadata. -/
private partial def visit (env : Environment) (n : Name)
    (seen : NameSet) : CommandElabM NameSet := do
  if seen.contains n then return seen
  let some ci := env.checked.get.find? n | throwError "missing dependency {n}"
  if ci.isUnsafe then throwError "unsafe dependency {n}"
  let ts := ci.type.getUsedConstants
  let vs := valueConstants ci
  let record := Json.mkObj [
    ("name", toJson n.toString), ("kind", toJson (kind ci)),
    ("type_constants", names ts), ("proof_constants", names vs)]
  logInfo m!"CERT_NODE|{record.compress}"
  let mut seen := seen.insert n
  for dep in ts ++ vs do
    seen ← visit env dep seen
  return seen

private def recordTarget (name : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.checked.get.find? name | throwError "missing target {name}"
  unless kind ci == "theorem" do throwError "target {name} is not a theorem"
  let axs ← Lean.collectAxioms name
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "forbidden axiom {ax} in {name}"
  let pp ← liftTermElabM <| withOptions (fun o => o.setBool `pp.all true) <| Meta.ppExpr ci.type
  let record := Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kind ci)),
    ("type_repr", toJson (reprStr ci.type)), ("type_pp_all", toJson pp.pretty),
    ("type_constants", names ci.type.getUsedConstants),
    ("proof_constants", names (valueConstants ci)), ("axioms", names axs)]
  logInfo m!"CERT_TARGET|{record.compress}"

elab "#cert_target " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  recordTarget name

/-- Numeric private-name components are Name.num, not quoted string atoms. -/
private def exactName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part =>
    match part.toNat? with
    | some k => .num n k
    | none => .str n part) .anonymous

elab "#cert_target_name " s:str : command => recordTarget (exactName s.getString)

elab "#cert_closure_names " ss:str* : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  for s in ss do
    seen ← visit env (exactName s.getString) seen
  logInfo m!"CERT_END|{seen.size}"

elab "#cert_closure " ns:ident* : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  for n in ns do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
    seen ← visit env name seen
  logInfo m!"CERT_END|{seen.size}"

/-- Record primitive definitions separately from theorem proof dependencies. -/
private def recordDefinition (name : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.checked.get.find? name | throwError "missing definition {name}"
  let .defnInfo v := ci | throwError "{name} is not a definition"
  if ci.isUnsafe then throwError "unsafe definition {name}"
  let record := Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kind ci)),
    ("type_repr", toJson (reprStr ci.type)),
    ("value_repr", toJson (reprStr v.value))]
  logInfo m!"CERT_DEFINITION|{record.compress}"

elab "#cert_definition " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  recordDefinition name

elab "#cert_definition_name " s:str : command => recordDefinition (exactName s.getString)

end Problem56.PaperV6
