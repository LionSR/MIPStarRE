import MIPStarRE.LDT.Test.MainTheorem.MainFormal
open Lean

def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`MIPStarRE).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => true

def canon (env : Environment) (closure : NameSet) (n : Name) : Name :=
  let s := n.toString
  let s := (s.splitOn "._proof_").head!
  let s := (s.splitOn ".match_").head!
  let s := (s.splitOn "._autoParam").head!
  let c := s.toName
  -- collapse only genuine structure-generated declarations into their parent
  let structural :=
    match env.find? c with
    | some (.ctorInfo v) => some v.induct
    | some (.recInfo v) => v.all.head?
    | _ =>
      if (env.getProjectionFnInfo? c).isSome then some c.getPrefix
      else none
  match structural with
  | some parent => if closure.contains parent then parent else c
  | none => c

/-- All local constants referenced by declaration `n`.
Mirrors comparator's `runForUsedConsts`: type + value (incl. theorem proofs)
+ inductive ctors + recursor rule RHSs. -/
def refsOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some ci =>
    let fromType := ci.type.getUsedConstants
    let fromValue := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    let extra : Array Name :=
      match ci with
      | .inductInfo v => v.ctors.toArray ++ v.all.toArray
      | .ctorInfo v => #[v.induct]
      | .recInfo v => v.rules.foldl (fun acc r => (acc.push r.ctor) ++ r.rhs.getUsedConstants) #[]
      | _ => #[]
    (fromType ++ fromValue ++ extra).filter (isLocal env)
  | none => #[]

partial def collect (env : Environment) (queue : List Name) (seen : NameSet) : NameSet :=
  match queue with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !isLocal env n then collect env rest seen
    else collect env ((refsOf env n).toList ++ rest) (seen.insert n)

def runExtract : MetaM Unit := do
  let env ← getEnv
  let some ci := env.find? `MIPStarRE.LDT.Test.mainFormal | throwError "not found"
  let roots := ci.type.getUsedConstants.toList.filter (isLocal env ·)
  let closure := collect env roots {}
  let mut canonSet : NameSet := {}
  for n in closure.toArray do
    canonSet := canonSet.insert (canon env closure n)
  -- topological ordering happens downstream in assemble_challenge.py
  -- (module import rank, then line number)
  for c in canonSet.toArray do
    let mod := match env.getModuleIdxFor? c with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    let path := mod.toString.replace "." "/" ++ ".lean"
    match ← Lean.findDeclarationRanges? c with
    | some r => IO.println s!"{c}\t{path}\t{r.range.pos.line}\t{r.range.endPos.line}"
    | none => IO.println s!"{c}\t{path}\tNORANGE\tNORANGE"

#eval runExtract
