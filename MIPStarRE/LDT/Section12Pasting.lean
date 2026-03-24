import MIPStarRE.LDT.Section12Pasting.Defs
import MIPStarRE.LDT.Section12Pasting.Sandwich
import MIPStarRE.LDT.Section12Pasting.Statements
import MIPStarRE.LDT.Section12Pasting.Theorems

/-!
Matching scaffold for Section 12 of the low individual degree paper in
`references/ldt-paper/ld-pasting.tex`.

This file still uses paper-local placeholders, but the main interfaces now name the
relevant complete/incomplete parts of the slice family, the completed family
`\widehat G`, the sandwich constructions, and the displayed error formulas that drive
later pasting arguments.

The content is split across four submodules:
- `Section12Pasting.Defs`: core definitions, abbreviations, and basic constructors
- `Section12Pasting.Sandwich`: switcheroo families, half-product/sandwich constructions
- `Section12Pasting.Statements`: displayed error terms and statement structures
- `Section12Pasting.Theorems`: theorem and lemma declarations
-/
