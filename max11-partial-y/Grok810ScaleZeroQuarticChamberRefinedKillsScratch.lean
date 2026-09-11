import Grok810ScaleZeroQuarticChamberRests6Scratch
import Grok810ScaleZeroQuarticPowerCertificatesScratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart101Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart103Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart104Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart105Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsPart44Scratch

/-! # Refined-leaf kills, `(8,10)` scale zero

22 of the 59 leaves of the 11 carrier-refined cells: 8 on a
single-monomial face of some carrier, 17 on the power systems
`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`
produced for exactly those cells.  The leaves come from the tournament
of `…ChamberRefineScratch`; their load columns are decided against the
leaf's *full* conjunct set (cell + refinement) in
`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.
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

section QuarticChamberRefinedKills810

/-! ## Top-coefficient bridges for the refined leaves -/

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
