import Lean

/-!
Local declaration-closure preflight, following the used-constant traversal of
Comparator 575674928e239f5bc452aab72d1dd7b0f1326494.
This compares trusted local .olean environments. It is not the sandboxed
export/NanoDa verifier; the Linux compatibility workflow performs that check.
-/

open Lean

deriving instance BEq for QuotKind
deriving instance BEq for QuotVal
deriving instance BEq for InductiveVal
deriving instance BEq for ConstantInfo

def targets : Array Name := #[`Problem56.main_universal_ose,
  `Problem56.PaperV6.fixed_frame_squared_norm_success]

def permitted : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]

def primitive : Array Name := #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow,
  ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor,
  ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
  ``List, ``eagerReduce]

def used (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then
    out := out ++ v.getUsedConstants
  match ci with
  | .inductInfo v => out := out ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    for r in v.rules do
      out := out.push r.ctor ++ r.rhs.getUsedConstants
  | _ => pure ()
  return out

def get (env : Environment) (n : Name) : IO ConstantInfo :=
  match env.find? n with
  | some ci => pure ci
  | none => throw <| IO.userError s!"Missing declaration {n}"

partial def matchClosure (challenge solution : Environment) (todo : Array Name)
    (seen : NameSet := {}) : IO NameSet := do
  if todo.isEmpty then return seen
  let n := todo.back!
  let todo := todo.pop
  if seen.contains n then return ← matchClosure challenge solution todo seen
  let c ← get challenge n
  let s ← get solution n
  if targets.contains n || permitted.contains n then
    unless c.toConstantVal == s.toConstantVal do
      throw <| IO.userError s!"Statement mismatch: {n}"
    match c, s with
    | .thmInfo _, .thmInfo _ | .axiomInfo _, .axiomInfo _ => pure ()
    | _, _ => throw <| IO.userError s!"Kind mismatch: {n}"
    matchClosure challenge solution (todo ++ s.type.getUsedConstants) (seen.insert n)
  else
    unless c == s do
      IO.FS.writeFile "/tmp/problem56-challenge-constant.txt" (reprStr c.type ++ "\nVALUE\n" ++ reprStr (c.value? (allowOpaque := true)))
      IO.FS.writeFile "/tmp/problem56-solution-constant.txt" (reprStr s.type ++ "\nVALUE\n" ++ reprStr (s.value? (allowOpaque := true)))
      throw <| IO.userError s!"Declaration mismatch: {n}"
    matchClosure challenge solution (todo ++ used s) (seen.insert n)

partial def proofClosure (env : Environment) (todo : Array Name)
    (seen : NameSet := {}) : IO NameSet := do
  if todo.isEmpty then return seen
  let n := todo.back!
  let todo := todo.pop
  if seen.contains n then return ← proofClosure env todo seen
  let ci ← get env n
  if ci.isUnsafe then throw <| IO.userError s!"Unsafe dependency: {n}"
  if ci.isAxiom && !permitted.contains n then
    throw <| IO.userError s!"Forbidden axiom: {n}"
  proofClosure env (todo ++ used ci) (seen.insert n)

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← importModules #[{module := `Challenge}] {}
  let solution ← importModules #[{module := `Solution}] {}
  let declarations ← matchClosure challenge solution (targets ++ permitted ++ primitive)
  let proofs ← proofClosure solution targets
  IO.println s!"DECLARATION_CLOSURE_PASS: {declarations.size} identical declarations; {proofs.size} proof dependencies; 2 public targets"
