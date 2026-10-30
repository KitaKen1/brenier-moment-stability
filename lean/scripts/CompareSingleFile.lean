import Lean

/-!
Statement comparison for the single-file edition.

`scripts/CompareStatement.lean` compares the challenge with the modular solution constant by
constant. That comparison is too strict for the single file. When a definition contains a
proof, Lean stores the proof in an auxiliary theorem `Foo._proof_n` and reuses an auxiliary
theorem that already has the same statement and proof. In one file the definitions of the
statement vocabulary come after the whole development, so they refer to auxiliary theorems
created earlier under other names, such as `BrenierMoment.tailEnvelope._proof_1` in place of
`BrenierStability.modulus._proof_1`. The definitions are the same up to these names.

Here every auxiliary theorem `Foo._proof_n` is replaced by its proof term before two
expressions are compared. After that the check is the one of `CompareStatement.lean`: for
every listed theorem, the two statements are equal, and every constant they depend on is
either imported by both sides from the same compiled module or declared on both sides with the
same kind, type and body. The axioms of the solution's proofs are checked against the
permitted list.

Run with the compiled challenge and the compiled single file on the search path:

  lean --run scripts/CompareSingleFile.lean CONFIG.json

where `CONFIG.json` names `challenge_module`, `solution_module`, `theorem_names` and
`permitted_axioms`.
-/

open Lean

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  permitted_axioms : Array String
deriving FromJson

def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- `Foo._proof_n`: an auxiliary theorem created for a proof inside a declaration. -/
def isAuxProof (env : Environment) (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_proof_" && (env.find? n matches some (.thmInfo _))
  | _ => false

/-- Replace every auxiliary proof constant by its proof term, recursively. -/
partial def inlineAux (env : Environment) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls =>
      if isAuxProof env n then
        match env.find? n with
        | some (.thmInfo t) => some (inlineAux env (t.value.instantiateLevelParams t.levelParams ls))
        | _ => none
      else none
    | _ => none

def sameRules (ea eb : Environment) : List RecursorRule → List RecursorRule → Bool
  | [], [] => true
  | a :: as, b :: bs =>
    a.ctor == b.ctor && a.nfields == b.nfields && inlineAux ea a.rhs == inlineAux eb b.rhs &&
      sameRules ea eb as bs
  | _, _ => false

/-- Same kind, universe parameters, type and body, after inlining auxiliary proofs. -/
def sameConst (ea eb : Environment) (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && inlineAux ea a.type == inlineAux eb b.type &&
  match a, b with
  | .defnInfo x, .defnInfo y => inlineAux ea x.value == inlineAux eb y.value && x.safety == y.safety
  | .thmInfo _, .thmInfo _ => true
  | .opaqueInfo x, .opaqueInfo y =>
    inlineAux ea x.value == inlineAux eb y.value && x.isUnsafe == y.isUnsafe
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | .quotInfo _, .quotInfo _ => true
  | .inductInfo x, .inductInfo y =>
    x.numParams == y.numParams && x.numIndices == y.numIndices && x.all == y.all &&
      x.ctors == y.ctors && x.isRec == y.isRec && x.isUnsafe == y.isUnsafe
  | .ctorInfo x, .ctorInfo y =>
    x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams &&
      x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y =>
    x.all == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.numMotives == y.numMotives && x.numMinors == y.numMinors && x.k == y.k &&
      x.isUnsafe == y.isUnsafe && sameRules ea eb x.rules y.rules
  | _, _ => false

/-- The constants of a declaration after inlining auxiliary proofs: its type, and its body
unless it is a theorem. -/
def usedConstants (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let mut result := (inlineAux env ci.type).getUsedConstants
  match ci with
  | .defnInfo x => result := result ++ (inlineAux env x.value).getUsedConstants
  | .opaqueInfo x => result := result ++ (inlineAux env x.value).getUsedConstants
  | .inductInfo x => result := result ++ x.ctors.toArray ++ x.all.toArray
  | .ctorInfo x => result := result.push x.induct
  | .recInfo x =>
    for rule in x.rules do
      result := result.push rule.ctor ++ (inlineAux env rule.rhs).getUsedConstants
  | _ => pure ()
  return result

/-- Compare the statement of `thm` and everything it depends on. Returns the constants that
are declared separately on the two sides and were compared. -/
def compareStatement (chal sol : Environment) (thm : Name) : IO (Array Name) := do
  let some c := chal.find? thm | throw <| IO.userError s!"challenge lacks {thm}"
  let some s := sol.find? thm | throw <| IO.userError s!"solution lacks {thm}"
  unless s matches .thmInfo _ do
    throw <| IO.userError s!"{thm} is not a theorem in the solution"
  unless c.levelParams == s.levelParams && inlineAux chal c.type == inlineAux sol s.type do
    throw <| IO.userError s!"{thm}: the two statements differ"
  let mut seen : NameSet := {}
  let mut todo : Array Name := (inlineAux chal c.type).getUsedConstants
  let mut compared : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some a := chal.find? n | throw <| IO.userError s!"challenge lacks {n}"
    let some b := sol.find? n | throw <| IO.userError s!"solution lacks {n}"
    match moduleOf chal n, moduleOf sol n with
    | some m₁, some m₂ =>
      -- A constant imported by both sides from one compiled module is literally the same.
      if m₁ == m₂ then continue
      unless sameConst chal sol a b do
        throw <| IO.userError s!"{n} is declared differently in {m₁} and {m₂}"
      compared := compared.push n
      todo := todo ++ usedConstants chal a
    | _, _ => throw <| IO.userError s!"{n} has no defining module"
  return compared

/-- Every axiom in the dependency cone of `thm`, proofs included. -/
def axiomsOf (env : Environment) (thm : Name) : IO (Array Name) := do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[thm]
  let mut found : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw <| IO.userError s!"unknown constant {n}"
    if ci matches .axiomInfo _ then found := found.push n
    for d in ci.getUsedConstantsAsSet do
      unless seen.contains d do todo := todo.push d
  return found

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | throw <| IO.userError "usage: CompareSingleFile.lean CONFIG.json"
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cfg ← IO.ofExcept (fromJson? json : Except String Config)
  initSearchPath (← findSysroot)
  let chal ← importModules #[{module := cfg.challenge_module.toName}] {}
  let sol ← importModules #[{module := cfg.solution_module.toName}] {}
  IO.println s!"challenge: {cfg.challenge_module}"
  IO.println s!"solution: {cfg.solution_module}"
  for t in cfg.theorem_names do
    let thm := t.toName
    let compared ← compareStatement chal sol thm
    let axioms ← axiomsOf sol thm
    let extra := axioms.filter fun a => !cfg.permitted_axioms.contains a.toString
    unless extra.isEmpty do
      throw <| IO.userError s!"{thm} uses axioms outside the permitted list: {extra}"
    let names := compared.qsort (fun a b => a.toString < b.toString)
    IO.println s!"{thm}: statement matches up to auxiliary proof names; {names.size} separately declared constants compared; axioms {axioms.qsort (fun a b => a.toString < b.toString)}"
    IO.println s!"  compared: {names}"
  IO.println "Single-file statement comparison passed."
  return 0
