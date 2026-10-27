import MIPStarRE

/-!
# Project simp-declaration extractor

This supplemental upload-planning query records project declarations in the
global simp set. Such declarations can be required while replaying tactics even
when the resulting proof term no longer references them.
-/

open Lean Meta

run_meta do
  let env ← getEnv
  let simpTheorems ← getSimpTheorems
  let projectPrefix := `MIPStarRE
  let moduleNames := env.header.moduleNames
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some moduleIndex := env.getModuleIdxFor? name | continue
    let some moduleName := moduleNames[moduleIndex.toNat]? | continue
    unless projectPrefix.isPrefixOf moduleName do continue
    if simpTheorems.isLemma (.decl name) then
      names := names.push name
  let sortedNames := names.qsort Name.quickLt
  IO.FS.writeFile "prove2me/extracted/simp_decls.txt"
    (String.intercalate "\n" (sortedNames.toList.map toString) ++ "\n")
  logInfo m!"wrote {sortedNames.size} project simp declarations"
