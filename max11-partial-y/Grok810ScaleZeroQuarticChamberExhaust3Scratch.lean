import Grok810ScaleZeroQuarticChamberExhaust2Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part0Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part1Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part2Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part3Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part4Scratch
import Grok810ScaleZeroQuarticChamberExhaust3Part5Scratch

/-! # Cost-argmin chamber exhaust (3/4), `(8,10)` scale zero

The 6 live-letter sets with |S| ∈ {5}.  Each theorem runs the case tree
of `CHAMBERS.md` §1: a linear tournament for `β = min s|_{B,C}`,
`q = min s|_{D,E}`, `r = min s|_{F,G}`, then `μ₂ = min(q,r)`,
`ω = min(β,q)`, then the three cost types `2μ₂`, `β+r`, `2β+ω`
against each other.  Branches no chamber matches are ℚ-infeasible
(exact Farkas certificates in
`scripts/check_810_quartic_chambers_lean.py`) and close by `omega`.
Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticChamberExhaust810

end QuarticChamberExhaust810

end Max11DegreeRoutes
