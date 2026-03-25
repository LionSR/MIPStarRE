import MIPStarRE.LDT.Pasting.Defs
import MIPStarRE.LDT.Pasting.Sandwich
import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Pasting.Theorems

/-!
Matching scaffold for Section 12 of the low individual degree paper in
`references/ldt-paper/ld-pasting.tex`.

This file still uses paper-local placeholders, but the main interfaces now name the
relevant complete/incomplete parts of the slice family, the completed family
`\widehat G`, the sandwich constructions, and the displayed error formulas that drive
later pasting arguments.

The content is split across four submodules:
- `Pasting.Defs`: core definitions, abbreviations, and basic constructors
- `Pasting.Sandwich`: switcheroo families, half-product/sandwich constructions
- `Pasting.Statements`: displayed error terms and statement structures
- `Pasting.Theorems`: theorem and lemma declarations
-/
