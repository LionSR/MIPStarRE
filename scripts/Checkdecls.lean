import Lean

open Lean

private def stringToName (s : String) : Name :=
  (s.splitOn ".").foldl
    (fun acc component =>
      match component.toNat? with
      | some n => Name.num acc n
      | none => Name.str acc component)
    Name.anonymous

private def moduleNameOfDecl? (decl : String) : Option Name := do
  let components := decl.splitOn "."
  let revComponents := components.reverse
  match revComponents with
  | [] | [_] => none
  | _declName :: revModule =>
      some <| revModule.reverse.foldl (fun acc component => Name.str acc component) Name.anonymous

private def parseDecls (contents : String) : Array (Nat × String) :=
  let lines := (contents.splitOn "\n").toArray
  let (decls, _) :=
    lines.foldl
      (fun state line =>
        let decls := state.1
        let lineNo := state.2
        let trimmed := line.trimAscii.toString
        let decls :=
          if trimmed.isEmpty || trimmed.startsWith "#" || trimmed.startsWith "--" then
            decls
          else
            decls.push (lineNo, trimmed)
        (decls, lineNo + 1))
      (#[], 1)
  decls

private def inferredModules
    (decls : Array (Nat × String)) : Except String (Array Import) := do
  let mut modules : Array Import := #[]
  for (_, decl) in decls do
    let some module := moduleNameOfDecl? decl
      | throw s!"Could not infer a module from declaration name {decl}."
    if modules.any (fun imp => imp.module == module) then
      continue
    modules := modules.push { module := module }
  return modules

private def missingDecls
    (env : Environment) (decls : Array (Nat × String)) : Array (Nat × String) :=
  decls.filter fun (_, decl) => env.find? (stringToName decl) |>.isNone

private def usage : String := "Usage: lake exe checkdecls blueprint/lean_decls"

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [pathStr] =>
      let path := System.FilePath.mk pathStr
      unless (← path.pathExists) do
        IO.eprintln s!"File not found: {path}"
        return 1
      let contents ← IO.FS.readFile path
      let decls := parseDecls contents
      let modules ←
        match inferredModules decls with
        | .ok modules => pure modules
        | .error err =>
            IO.eprintln err
            return 1
      initSearchPath (← findSysroot)
      enableInitializersExecution
      let env ← importModules modules {} (trustLevel := 1024)
      let missing := missingDecls env decls
      if missing.isEmpty then
        IO.println s!"All {decls.size} declarations from {path} resolved."
        return 0
      IO.eprintln s!"Missing {missing.size} declaration(s) listed in {path}:"
      for (lineNo, decl) in missing do
        IO.eprintln s!"  line {lineNo}: {decl}"
      return 1
  | _ =>
      IO.eprintln usage
      return 1
