import Lean

/-!
# Syntax identifier extractor

This supplemental upload oracle records exact source ranges for identifiers
inside parsed command syntax, including identifiers contained in quotations and
macro bodies that do not receive `TermInfo` entries during elaboration.
-/

open Lean Elab Parser

def syntaxPosJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [
    ("line", toJson pos.line),
    ("col", toJson pos.column),
    ("offset", toJson p.byteIdx)
  ]

def platformTacticName? (kind : Name) : Option Name :=
  let value := kind.toString
  if value.endsWith "quantumNonneg" then
    some `quantum_nonneg
  else if value.endsWith "avgCongr" then
    some `avg_congr
  else
    none

partial def collectSyntaxIdentifiers (stx : Syntax)
    (acc : Array (String × Name × String.Pos.Raw × String.Pos.Raw)) :
    Array (String × Name × String.Pos.Raw × String.Pos.Raw) :=
  let acc :=
    if stx.isIdent then
      match stx.getPos?, stx.getTailPos? with
      | some start, some finish => acc.push ("syntaxIdentifier", stx.getId, start, finish)
      | _, _ => acc
    else
      acc
  let acc :=
    match platformTacticName? stx.getKind, stx.getPos?, stx.getTailPos? with
    | some name, some start, some finish =>
        acc.push ("platformTactic", name, start, finish)
    | _, _, _ => acc
  stx.getArgs.foldl (fun result child => collectSyntaxIdentifiers child result) acc

unsafe def main (args : List String) : IO UInt32 := do
  let some fileName := args[0]? | do
    IO.eprintln "usage: lake env lean --run extract_syntax_identifiers.lean <File.lean>"
    return 1
  let input ← IO.FS.readFile (⟨fileName⟩ : System.FilePath)
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let cmdState := Command.mkState env messages {}
  let state ← IO.processCommands inputCtx parserState cmdState
  if state.commandState.messages.hasErrors then
    for message in state.commandState.messages.toList do
      IO.eprintln (← message.toString)
    return 1
  let fm := inputCtx.fileMap
  let mut identifiers : Array (String × Name × String.Pos.Raw × String.Pos.Raw) := #[]
  for command in state.commands do
    identifiers := collectSyntaxIdentifiers command identifiers
  let sortedIdentifiers :=
    identifiers.qsort fun (_, _, startA, _) (_, _, startB, _) => startA < startB
  for (kind, name, start, finish) in sortedIdentifiers do
    if kind == "platformTactic" || name.toString.contains "MIPStarRE" then
      IO.println (Json.mkObj [
        ("kind", Json.str kind),
        ("name", Json.str name.toString),
        ("start", syntaxPosJson fm start),
        ("end", syntaxPosJson fm finish)
      ]).compress
  return 0
