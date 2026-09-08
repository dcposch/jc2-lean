import Grok810ScaleZeroQuarticChamberExhaust3Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part0Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part1Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part2Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part3Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part4Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part5Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part6Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part7Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part8Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part9Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part10Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part11Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part12Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part13Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part14Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part15Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part16Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part17Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part18Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part19Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part20Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part21Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part22Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part23Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part24Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part25Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part26Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part27Scratch
import Grok810ScaleZeroQuarticChamberExhaust4Part28Scratch

/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
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

#print axioms quarticChamberSupport810_of

end Max11DegreeRoutes
