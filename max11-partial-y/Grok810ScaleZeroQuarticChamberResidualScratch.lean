import Grok810ScaleZeroQuarticChamberExhaust4Part1Scratch
import Grok810ScaleZeroQuarticChamberKillsScratch

/-! # Residual after Files B/C, `(8,10)` scale zero

`QuarticChamberResidual810`, the 565-constructor inductive of the
cost-argmin chambers the level-0 kills do not reach, and
`normalized810ScaleZero_quarticChamberResidual`, which routes the
1115-chamber exhaust through the 550 single-monomial kills.
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

section QuarticChamberResidual810

variable [IsAlgClosed k]

/-! ## What the chamber ladder leaves -/

set_option maxHeartbeats 64000000 in
/-- The 565 cost-argmin chambers Files B/C do not close: the
two genuinely open leaves, the 19 deep-rescue leaves, the 64
weak-band leaves, the 12 `no_monomial_target` leaves, the
`power_target` leaves (whose kill needs a `_coeff_top` extraction),
and every leaf whose κ band is unusable (`ζ`/`θ` with `B` or `C`
live) or which needs a `γ/ε/η` band (corner `H`). -/
inductive QuarticChamberResidual810 (A B C D E F G : k[X]) : Prop
  | rB0 : QuarticChamberB0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rC0 : QuarticChamberC0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rE0 : QuarticChamberE0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rG0 : QuarticChamberG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBC0 : QuarticChamberBC0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBC1 : QuarticChamberBC1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBD0 : QuarticChamberBD0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBD2 : QuarticChamberBD2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBE0 : QuarticChamberBE0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBE2 : QuarticChamberBE2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBF0 : QuarticChamberBF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBF2 : QuarticChamberBF2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBG0 : QuarticChamberBG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBG1 : QuarticChamberBG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBG2 : QuarticChamberBG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCD2 : QuarticChamberCD2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCE2 : QuarticChamberCE2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCF1 : QuarticChamberCF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCG1 : QuarticChamberCG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCG2 : QuarticChamberCG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCG3 : QuarticChamberCG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDE1 : QuarticChamberDE1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDF1 : QuarticChamberDF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDG0 : QuarticChamberDG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDG1 : QuarticChamberDG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rEF0 : QuarticChamberEF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rEF1 : QuarticChamberEF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rEG0 : QuarticChamberEG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rEG1 : QuarticChamberEG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rFG0 : QuarticChamberFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rFG1 : QuarticChamberFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCD0 : QuarticChamberBCD0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCD1 : QuarticChamberBCD1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCD4 : QuarticChamberBCD4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCD5 : QuarticChamberBCD5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCD6 : QuarticChamberBCD6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCE0 : QuarticChamberBCE0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCE1 : QuarticChamberBCE1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCE4 : QuarticChamberBCE4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCE5 : QuarticChamberBCE5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCE6 : QuarticChamberBCE6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCF0 : QuarticChamberBCF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCF1 : QuarticChamberBCF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCF3 : QuarticChamberBCF3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCF5 : QuarticChamberBCF5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCF9 : QuarticChamberBCF9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCG0 : QuarticChamberBCG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCG1 : QuarticChamberBCG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCG2 : QuarticChamberBCG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCG3 : QuarticChamberBCG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCG5 : QuarticChamberBCG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCG10 : QuarticChamberBCG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDE0 : QuarticChamberBDE0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDE2 : QuarticChamberBDE2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDE3 : QuarticChamberBDE3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDE4 : QuarticChamberBDE4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDE6 : QuarticChamberBDE6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDF0 : QuarticChamberBDF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDF2 : QuarticChamberBDF2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDF3 : QuarticChamberBDF3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDF4 : QuarticChamberBDF4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDF8 : QuarticChamberBDF8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDF9 : QuarticChamberBDF9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDG0 : QuarticChamberBDG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDG1 : QuarticChamberBDG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDG2 : QuarticChamberBDG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDG4 : QuarticChamberBDG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDG8 : QuarticChamberBDG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEF0 : QuarticChamberBEF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEF2 : QuarticChamberBEF2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEF3 : QuarticChamberBEF3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEF4 : QuarticChamberBEF4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEF8 : QuarticChamberBEF8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEG0 : QuarticChamberBEG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEG1 : QuarticChamberBEG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEG2 : QuarticChamberBEG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEG4 : QuarticChamberBEG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEG8 : QuarticChamberBEG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBFG0 : QuarticChamberBFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBFG2 : QuarticChamberBFG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBFG4 : QuarticChamberBFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBFG7 : QuarticChamberBFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBFG8 : QuarticChamberBFG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDE2 : QuarticChamberCDE2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDE3 : QuarticChamberCDE3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDE4 : QuarticChamberCDE4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDE6 : QuarticChamberCDE6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDF1 : QuarticChamberCDF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDF4 : QuarticChamberCDF4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDF5 : QuarticChamberCDF5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDF8 : QuarticChamberCDF8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDF9 : QuarticChamberCDF9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDG1 : QuarticChamberCDG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDG2 : QuarticChamberCDG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDG3 : QuarticChamberCDG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDG4 : QuarticChamberCDG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDG6 : QuarticChamberCDG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDG8 : QuarticChamberCDG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEF1 : QuarticChamberCEF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEF4 : QuarticChamberCEF4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEF8 : QuarticChamberCEF8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEG1 : QuarticChamberCEG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEG2 : QuarticChamberCEG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEG4 : QuarticChamberCEG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEG6 : QuarticChamberCEG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCFG1 : QuarticChamberCFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCFG3 : QuarticChamberCFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCFG4 : QuarticChamberCFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCFG5 : QuarticChamberCFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCFG7 : QuarticChamberCFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCFG8 : QuarticChamberCFG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCFG9 : QuarticChamberCFG9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEF2 : QuarticChamberDEF2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEF3 : QuarticChamberDEF3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEG0 : QuarticChamberDEG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEG2 : QuarticChamberDEG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEG3 : QuarticChamberDEG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEG4 : QuarticChamberDEG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEG5 : QuarticChamberDEG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDFG0 : QuarticChamberDFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDFG1 : QuarticChamberDFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDFG2 : QuarticChamberDFG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDFG3 : QuarticChamberDFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rEFG0 : QuarticChamberEFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rEFG1 : QuarticChamberEFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rEFG2 : QuarticChamberEFG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rEFG3 : QuarticChamberEFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE0 : QuarticChamberBCDE0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE1 : QuarticChamberBCDE1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE4 : QuarticChamberBCDE4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE5 : QuarticChamberBCDE5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE6 : QuarticChamberBCDE6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE7 : QuarticChamberBCDE7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE8 : QuarticChamberBCDE8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE9 : QuarticChamberBCDE9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE10 : QuarticChamberBCDE10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE12 : QuarticChamberBCDE12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDE13 : QuarticChamberBCDE13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF0 : QuarticChamberBCDF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF1 : QuarticChamberBCDF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF3 : QuarticChamberBCDF3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF5 : QuarticChamberBCDF5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF6 : QuarticChamberBCDF6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF7 : QuarticChamberBCDF7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF11 : QuarticChamberBCDF11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF15 : QuarticChamberBCDF15810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF18 : QuarticChamberBCDF18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF19 : QuarticChamberBCDF19810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF22 : QuarticChamberBCDF22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF23 : QuarticChamberBCDF23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF24 : QuarticChamberBCDF24810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDF25 : QuarticChamberBCDF25810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG0 : QuarticChamberBCDG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG1 : QuarticChamberBCDG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG2 : QuarticChamberBCDG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG3 : QuarticChamberBCDG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG5 : QuarticChamberBCDG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG6 : QuarticChamberBCDG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG7 : QuarticChamberBCDG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG11 : QuarticChamberBCDG11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG16 : QuarticChamberBCDG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG17 : QuarticChamberBCDG17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG18 : QuarticChamberBCDG18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG22 : QuarticChamberBCDG22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG23 : QuarticChamberBCDG23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDG24 : QuarticChamberBCDG24810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF0 : QuarticChamberBCEF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF1 : QuarticChamberBCEF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF3 : QuarticChamberBCEF3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF5 : QuarticChamberBCEF5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF6 : QuarticChamberBCEF6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF7 : QuarticChamberBCEF7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF11 : QuarticChamberBCEF11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF15 : QuarticChamberBCEF15810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF18 : QuarticChamberBCEF18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF22 : QuarticChamberBCEF22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEF23 : QuarticChamberBCEF23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG0 : QuarticChamberBCEG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG1 : QuarticChamberBCEG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG2 : QuarticChamberBCEG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG3 : QuarticChamberBCEG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG5 : QuarticChamberBCEG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG6 : QuarticChamberBCEG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG7 : QuarticChamberBCEG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG11 : QuarticChamberBCEG11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG16 : QuarticChamberBCEG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG17 : QuarticChamberBCEG17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG18 : QuarticChamberBCEG18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG22 : QuarticChamberBCEG22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG23 : QuarticChamberBCEG23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEG24 : QuarticChamberBCEG24810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG0 : QuarticChamberBCFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG1 : QuarticChamberBCFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG3 : QuarticChamberBCFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG5 : QuarticChamberBCFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG7 : QuarticChamberBCFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG11 : QuarticChamberBCFG11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG14 : QuarticChamberBCFG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG15 : QuarticChamberBCFG15810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG17 : QuarticChamberBCFG17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG21 : QuarticChamberBCFG21810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG24 : QuarticChamberBCFG24810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCFG28 : QuarticChamberBCFG28810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF0 : QuarticChamberBDEF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF2 : QuarticChamberBDEF2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF4 : QuarticChamberBDEF4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF6 : QuarticChamberBDEF6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF7 : QuarticChamberBDEF7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF10 : QuarticChamberBDEF10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF14 : QuarticChamberBDEF14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF16 : QuarticChamberBDEF16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF17 : QuarticChamberBDEF17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF18 : QuarticChamberBDEF18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEF20 : QuarticChamberBDEF20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG0 : QuarticChamberBDEG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG1 : QuarticChamberBDEG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG2 : QuarticChamberBDEG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG4 : QuarticChamberBDEG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG7 : QuarticChamberBDEG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG10 : QuarticChamberBDEG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG14 : QuarticChamberBDEG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG16 : QuarticChamberBDEG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG17 : QuarticChamberBDEG17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEG20 : QuarticChamberBDEG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG0 : QuarticChamberBDFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG2 : QuarticChamberBDFG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG4 : QuarticChamberBDFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG5 : QuarticChamberBDFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG6 : QuarticChamberBDFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG7 : QuarticChamberBDFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG10 : QuarticChamberBDFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG13 : QuarticChamberBDFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG14 : QuarticChamberBDFG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG16 : QuarticChamberBDFG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG20 : QuarticChamberBDFG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG21 : QuarticChamberBDFG21810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDFG22 : QuarticChamberBDFG22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG0 : QuarticChamberBEFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG2 : QuarticChamberBEFG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG4 : QuarticChamberBEFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG5 : QuarticChamberBEFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG6 : QuarticChamberBEFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG7 : QuarticChamberBEFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG10 : QuarticChamberBEFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG13 : QuarticChamberBEFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG14 : QuarticChamberBEFG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG16 : QuarticChamberBEFG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBEFG20 : QuarticChamberBEFG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF1 : QuarticChamberCDEF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF4 : QuarticChamberCDEF4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF7 : QuarticChamberCDEF7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF8 : QuarticChamberCDEF8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF10 : QuarticChamberCDEF10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF14 : QuarticChamberCDEF14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF16 : QuarticChamberCDEF16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF17 : QuarticChamberCDEF17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEF18 : QuarticChamberCDEF18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG1 : QuarticChamberCDEG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG2 : QuarticChamberCDEG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG3 : QuarticChamberCDEG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG4 : QuarticChamberCDEG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG6 : QuarticChamberCDEG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG7 : QuarticChamberCDEG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG9 : QuarticChamberCDEG9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG10 : QuarticChamberCDEG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG12 : QuarticChamberCDEG12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG14 : QuarticChamberCDEG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG16 : QuarticChamberCDEG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG17 : QuarticChamberCDEG17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEG20 : QuarticChamberCDEG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG1 : QuarticChamberCDFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG3 : QuarticChamberCDFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG4 : QuarticChamberCDFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG5 : QuarticChamberCDFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG6 : QuarticChamberCDFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG7 : QuarticChamberCDFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG8 : QuarticChamberCDFG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG10 : QuarticChamberCDFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG11 : QuarticChamberCDFG11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG13 : QuarticChamberCDFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG14 : QuarticChamberCDFG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG15 : QuarticChamberCDFG15810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG16 : QuarticChamberCDFG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG18 : QuarticChamberCDFG18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG20 : QuarticChamberCDFG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG21 : QuarticChamberCDFG21810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDFG22 : QuarticChamberCDFG22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG1 : QuarticChamberCEFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG3 : QuarticChamberCEFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG4 : QuarticChamberCEFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG5 : QuarticChamberCEFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG6 : QuarticChamberCEFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG7 : QuarticChamberCEFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG8 : QuarticChamberCEFG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG10 : QuarticChamberCEFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG13 : QuarticChamberCEFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG14 : QuarticChamberCEFG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG15 : QuarticChamberCEFG15810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG16 : QuarticChamberCEFG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG18 : QuarticChamberCEFG18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCEFG20 : QuarticChamberCEFG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG0 : QuarticChamberDEFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG1 : QuarticChamberDEFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG4 : QuarticChamberDEFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG5 : QuarticChamberDEFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG6 : QuarticChamberDEFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG7 : QuarticChamberDEFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG8 : QuarticChamberDEFG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG9 : QuarticChamberDEFG9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG10 : QuarticChamberDEFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rDEFG11 : QuarticChamberDEFG11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF0 : QuarticChamberBCDEF0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF1 : QuarticChamberBCDEF1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF3 : QuarticChamberBCDEF3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF5 : QuarticChamberBCDEF5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF6 : QuarticChamberBCDEF6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF7 : QuarticChamberBCDEF7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF10 : QuarticChamberBCDEF10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF12 : QuarticChamberBCDEF12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF13 : QuarticChamberBCDEF13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF17 : QuarticChamberBCDEF17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF19 : QuarticChamberBCDEF19810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF20 : QuarticChamberBCDEF20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF23 : QuarticChamberBCDEF23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF27 : QuarticChamberBCDEF27810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF30 : QuarticChamberBCDEF30810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF33 : QuarticChamberBCDEF33810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF34 : QuarticChamberBCDEF34810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF36 : QuarticChamberBCDEF36810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF40 : QuarticChamberBCDEF40810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF41 : QuarticChamberBCDEF41810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF42 : QuarticChamberBCDEF42810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF44 : QuarticChamberBCDEF44810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF45 : QuarticChamberBCDEF45810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF46 : QuarticChamberBCDEF46810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF47 : QuarticChamberBCDEF47810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF48 : QuarticChamberBCDEF48810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF50 : QuarticChamberBCDEF50810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEF51 : QuarticChamberBCDEF51810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG0 : QuarticChamberBCDEG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG1 : QuarticChamberBCDEG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG2 : QuarticChamberBCDEG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG3 : QuarticChamberBCDEG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG5 : QuarticChamberBCDEG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG6 : QuarticChamberBCDEG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG7 : QuarticChamberBCDEG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG10 : QuarticChamberBCDEG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG12 : QuarticChamberBCDEG12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG13 : QuarticChamberBCDEG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG17 : QuarticChamberBCDEG17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG20 : QuarticChamberBCDEG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG23 : QuarticChamberBCDEG23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG28 : QuarticChamberBCDEG28810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG30 : QuarticChamberBCDEG30810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG32 : QuarticChamberBCDEG32810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG33 : QuarticChamberBCDEG33810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG36 : QuarticChamberBCDEG36810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG40 : QuarticChamberBCDEG40810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG41 : QuarticChamberBCDEG41810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG42 : QuarticChamberBCDEG42810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG44 : QuarticChamberBCDEG44810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG45 : QuarticChamberBCDEG45810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG46 : QuarticChamberBCDEG46810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG47 : QuarticChamberBCDEG47810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG50 : QuarticChamberBCDEG50810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEG51 : QuarticChamberBCDEG51810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG0 : QuarticChamberBCDFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG1 : QuarticChamberBCDFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG3 : QuarticChamberBCDFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG5 : QuarticChamberBCDFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG6 : QuarticChamberBCDFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG7 : QuarticChamberBCDFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG9 : QuarticChamberBCDFG9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG10 : QuarticChamberBCDFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG12 : QuarticChamberBCDFG12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG13 : QuarticChamberBCDFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG14 : QuarticChamberBCDFG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG17 : QuarticChamberBCDFG17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG18 : QuarticChamberBCDFG18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG19 : QuarticChamberBCDFG19810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG23 : QuarticChamberBCDFG23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG26 : QuarticChamberBCDFG26810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG27 : QuarticChamberBCDFG27810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG29 : QuarticChamberBCDFG29810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG30 : QuarticChamberBCDFG30810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG31 : QuarticChamberBCDFG31810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG35 : QuarticChamberBCDFG35810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG39 : QuarticChamberBCDFG39810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG42 : QuarticChamberBCDFG42810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG43 : QuarticChamberBCDFG43810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG44 : QuarticChamberBCDFG44810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG45 : QuarticChamberBCDFG45810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG48 : QuarticChamberBCDFG48810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG49 : QuarticChamberBCDFG49810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG52 : QuarticChamberBCDFG52810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG54 : QuarticChamberBCDFG54810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG58 : QuarticChamberBCDFG58810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG59 : QuarticChamberBCDFG59810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG60 : QuarticChamberBCDFG60810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG61 : QuarticChamberBCDFG61810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDFG62 : QuarticChamberBCDFG62810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG0 : QuarticChamberBCEFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG1 : QuarticChamberBCEFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG3 : QuarticChamberBCEFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG5 : QuarticChamberBCEFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG6 : QuarticChamberBCEFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG7 : QuarticChamberBCEFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG9 : QuarticChamberBCEFG9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG10 : QuarticChamberBCEFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG12 : QuarticChamberBCEFG12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG13 : QuarticChamberBCEFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG14 : QuarticChamberBCEFG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG17 : QuarticChamberBCEFG17810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG18 : QuarticChamberBCEFG18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG19 : QuarticChamberBCEFG19810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG23 : QuarticChamberBCEFG23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG26 : QuarticChamberBCEFG26810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG27 : QuarticChamberBCEFG27810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG29 : QuarticChamberBCEFG29810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG30 : QuarticChamberBCEFG30810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG31 : QuarticChamberBCEFG31810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG35 : QuarticChamberBCEFG35810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG39 : QuarticChamberBCEFG39810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG42 : QuarticChamberBCEFG42810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG43 : QuarticChamberBCEFG43810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG44 : QuarticChamberBCEFG44810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG45 : QuarticChamberBCEFG45810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG48 : QuarticChamberBCEFG48810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG52 : QuarticChamberBCEFG52810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG54 : QuarticChamberBCEFG54810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG58 : QuarticChamberBCEFG58810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCEFG59 : QuarticChamberBCEFG59810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG0 : QuarticChamberBDEFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG2 : QuarticChamberBDEFG2810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG4 : QuarticChamberBDEFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG5 : QuarticChamberBDEFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG6 : QuarticChamberBDEFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG7 : QuarticChamberBDEFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG8 : QuarticChamberBDEFG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG9 : QuarticChamberBDEFG9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG10 : QuarticChamberBDEFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG11 : QuarticChamberBDEFG11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG12 : QuarticChamberBDEFG12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG13 : QuarticChamberBDEFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG16 : QuarticChamberBDEFG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG18 : QuarticChamberBDEFG18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG19 : QuarticChamberBDEFG19810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG22 : QuarticChamberBDEFG22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG25 : QuarticChamberBDEFG25810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG26 : QuarticChamberBDEFG26810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG28 : QuarticChamberBDEFG28810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG31 : QuarticChamberBDEFG31810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG34 : QuarticChamberBDEFG34810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG38 : QuarticChamberBDEFG38810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG39 : QuarticChamberBDEFG39810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG42 : QuarticChamberBDEFG42810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG43 : QuarticChamberBDEFG43810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG44 : QuarticChamberBDEFG44810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG45 : QuarticChamberBDEFG45810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBDEFG48 : QuarticChamberBDEFG48810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG1 : QuarticChamberCDEFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG3 : QuarticChamberCDEFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG4 : QuarticChamberCDEFG4810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG5 : QuarticChamberCDEFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG6 : QuarticChamberCDEFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG7 : QuarticChamberCDEFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG8 : QuarticChamberCDEFG8810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG9 : QuarticChamberCDEFG9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG10 : QuarticChamberCDEFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG11 : QuarticChamberCDEFG11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG12 : QuarticChamberCDEFG12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG13 : QuarticChamberCDEFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG14 : QuarticChamberCDEFG14810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG16 : QuarticChamberCDEFG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG19 : QuarticChamberCDEFG19810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG20 : QuarticChamberCDEFG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG22 : QuarticChamberCDEFG22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG25 : QuarticChamberCDEFG25810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG26 : QuarticChamberCDEFG26810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG28 : QuarticChamberCDEFG28810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG30 : QuarticChamberCDEFG30810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG31 : QuarticChamberCDEFG31810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG34 : QuarticChamberCDEFG34810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG36 : QuarticChamberCDEFG36810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG38 : QuarticChamberCDEFG38810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG39 : QuarticChamberCDEFG39810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG42 : QuarticChamberCDEFG42810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG43 : QuarticChamberCDEFG43810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG44 : QuarticChamberCDEFG44810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rCDEFG45 : QuarticChamberCDEFG45810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG0 : QuarticChamberBCDEFG0810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG1 : QuarticChamberBCDEFG1810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG3 : QuarticChamberBCDEFG3810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG5 : QuarticChamberBCDEFG5810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG6 : QuarticChamberBCDEFG6810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG7 : QuarticChamberBCDEFG7810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG9 : QuarticChamberBCDEFG9810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG10 : QuarticChamberBCDEFG10810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG11 : QuarticChamberBCDEFG11810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG12 : QuarticChamberBCDEFG12810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG13 : QuarticChamberBCDEFG13810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG15 : QuarticChamberBCDEFG15810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG16 : QuarticChamberBCDEFG16810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG18 : QuarticChamberBCDEFG18810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG19 : QuarticChamberBCDEFG19810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG20 : QuarticChamberBCDEFG20810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG21 : QuarticChamberBCDEFG21810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG22 : QuarticChamberBCDEFG22810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG23 : QuarticChamberBCDEFG23810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG24 : QuarticChamberBCDEFG24810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG25 : QuarticChamberBCDEFG25810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG26 : QuarticChamberBCDEFG26810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG29 : QuarticChamberBCDEFG29810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG30 : QuarticChamberBCDEFG30810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG31 : QuarticChamberBCDEFG31810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG34 : QuarticChamberBCDEFG34810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG36 : QuarticChamberBCDEFG36810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG37 : QuarticChamberBCDEFG37810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG41 : QuarticChamberBCDEFG41810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG43 : QuarticChamberBCDEFG43810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG44 : QuarticChamberBCDEFG44810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG47 : QuarticChamberBCDEFG47810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG50 : QuarticChamberBCDEFG50810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG51 : QuarticChamberBCDEFG51810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG53 : QuarticChamberBCDEFG53810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG54 : QuarticChamberBCDEFG54810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG55 : QuarticChamberBCDEFG55810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG58 : QuarticChamberBCDEFG58810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG60 : QuarticChamberBCDEFG60810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG61 : QuarticChamberBCDEFG61810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG65 : QuarticChamberBCDEFG65810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG68 : QuarticChamberBCDEFG68810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG71 : QuarticChamberBCDEFG71810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG75 : QuarticChamberBCDEFG75810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG78 : QuarticChamberBCDEFG78810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG79 : QuarticChamberBCDEFG79810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG80 : QuarticChamberBCDEFG80810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG81 : QuarticChamberBCDEFG81810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG82 : QuarticChamberBCDEFG82810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG83 : QuarticChamberBCDEFG83810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG84 : QuarticChamberBCDEFG84810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG85 : QuarticChamberBCDEFG85810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG86 : QuarticChamberBCDEFG86810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG87 : QuarticChamberBCDEFG87810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG90 : QuarticChamberBCDEFG90810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG93 : QuarticChamberBCDEFG93810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG94 : QuarticChamberBCDEFG94810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG96 : QuarticChamberBCDEFG96810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG100 : QuarticChamberBCDEFG100810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG102 : QuarticChamberBCDEFG102810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG104 : QuarticChamberBCDEFG104810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG105 : QuarticChamberBCDEFG105810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG108 : QuarticChamberBCDEFG108810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG112 : QuarticChamberBCDEFG112810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG113 : QuarticChamberBCDEFG113810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG114 : QuarticChamberBCDEFG114810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG115 : QuarticChamberBCDEFG115810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG118 : QuarticChamberBCDEFG118810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG119 : QuarticChamberBCDEFG119810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG120 : QuarticChamberBCDEFG120810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG121 : QuarticChamberBCDEFG121810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG122 : QuarticChamberBCDEFG122810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG123 : QuarticChamberBCDEFG123810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG126 : QuarticChamberBCDEFG126810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G
  | rBCDEFG127 : QuarticChamberBCDEFG127810 A B C D E F G →
      QuarticChamberResidual810 A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Honest leftover after Files B/C of the σ-defect ladder.

Closed relative to `normalized810ScaleZero_quarticLoadLadderResidual`:
the 1115-chamber cost-argmin exhaust and the 550 chambers whose
level-0 certificate is a single monomial and whose eight load
columns are empty, dominated, or covered by the κ ladder's band.
Remaining: the all-constant corner (`l = β = δ = ζ = 0`) and the
565 chambers of `QuarticChamberResidual810`.  Next unused row:
the `power_target` and `no_monomial_target` kills (`_coeff_top` plus
the certificates of `Grok810ScaleZeroQuarticChamberCertificatesScratch`),
then the `N₂/N₅/N₇` load ladder of
`Grok810ScaleZeroQuarticChamberAuxTowerScratch` for the `ζ`/`θ`
columns κ cannot reach, then corner `H` (`γ/ε/η`).
No `sorry`, no new axioms, no finite-root shortcut. -/
theorem normalized810ScaleZero_quarticChamberResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0 ∧
              B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
              E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0) ∨
            QuarticChamberResidual810 A B C D E F G)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticLoadLadderResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · obtain ⟨hconeA, hexh, hlK, hbK, hdK, hzK, htK, hconst, hevenC, hevenE⟩ := hA
    refine Or.inl ⟨hconeA, ?_⟩
    by_cases hnc : B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0
    · rcases hconst with ⟨hl0, hb0, hd0, hz0⟩ | hn
      · exact Or.inl ⟨hl0, hb0, hd0, hz0, hnc.1, hnc.2.1, hnc.2.2.1,
          hnc.2.2.2.1, hnc.2.2.2.2.1, hnc.2.2.2.2.2⟩
      · exact absurd hnc hn
    · refine Or.inr ?_
      have hsupp := quarticChamberSupport810_of (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G hconeA
        hjdiv hder
      cases hsupp with
      | size1 h =>
        cases h with
        | cB0 hc =>
          exact QuarticChamberResidual810.rB0 hc
        | cC0 hc =>
          exact QuarticChamberResidual810.rC0 hc
        | cD0 hc =>
          exact (quarticChamberD0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cE0 hc =>
          exact QuarticChamberResidual810.rE0 hc
        | cF0 hc =>
          exact (quarticChamberF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cG0 hc =>
          exact QuarticChamberResidual810.rG0 hc
      | size2 h =>
        cases h with
        | cBC0 hc =>
          exact QuarticChamberResidual810.rBC0 hc
        | cBC1 hc =>
          exact QuarticChamberResidual810.rBC1 hc
        | cBC2 hc =>
          exact (quarticChamberBC2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBD0 hc =>
          exact QuarticChamberResidual810.rBD0 hc
        | cBD1 hc =>
          exact (quarticChamberBD1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBD2 hc =>
          exact QuarticChamberResidual810.rBD2 hc
        | cBE0 hc =>
          exact QuarticChamberResidual810.rBE0 hc
        | cBE1 hc =>
          exact (quarticChamberBE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBE2 hc =>
          exact QuarticChamberResidual810.rBE2 hc
        | cBF0 hc =>
          exact QuarticChamberResidual810.rBF0 hc
        | cBF1 hc =>
          exact (quarticChamberBF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBF2 hc =>
          exact QuarticChamberResidual810.rBF2 hc
        | cBF3 hc =>
          exact (quarticChamberBF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBF4 hc =>
          exact (quarticChamberBF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBG0 hc =>
          exact QuarticChamberResidual810.rBG0 hc
        | cBG1 hc =>
          exact QuarticChamberResidual810.rBG1 hc
        | cBG2 hc =>
          exact QuarticChamberResidual810.rBG2 hc
        | cBG3 hc =>
          exact (quarticChamberBG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBG4 hc =>
          exact (quarticChamberBG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCD0 hc =>
          exact (quarticChamberCD0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCD1 hc =>
          exact (quarticChamberCD1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCD2 hc =>
          exact QuarticChamberResidual810.rCD2 hc
        | cCE0 hc =>
          exact (quarticChamberCE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCE1 hc =>
          exact (quarticChamberCE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCE2 hc =>
          exact QuarticChamberResidual810.rCE2 hc
        | cCF0 hc =>
          exact (quarticChamberCF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCF1 hc =>
          exact QuarticChamberResidual810.rCF1 hc
        | cCF2 hc =>
          exact (quarticChamberCF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCF3 hc =>
          exact (quarticChamberCF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCF4 hc =>
          exact (quarticChamberCF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCG0 hc =>
          exact (quarticChamberCG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCG1 hc =>
          exact QuarticChamberResidual810.rCG1 hc
        | cCG2 hc =>
          exact QuarticChamberResidual810.rCG2 hc
        | cCG3 hc =>
          exact QuarticChamberResidual810.rCG3 hc
        | cCG4 hc =>
          exact (quarticChamberCG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDE0 hc =>
          exact (quarticChamberDE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDE1 hc =>
          exact QuarticChamberResidual810.rDE1 hc
        | cDE2 hc =>
          exact (quarticChamberDE2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDF0 hc =>
          exact (quarticChamberDF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDF1 hc =>
          exact QuarticChamberResidual810.rDF1 hc
        | cDF2 hc =>
          exact (quarticChamberDF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDG0 hc =>
          exact QuarticChamberResidual810.rDG0 hc
        | cDG1 hc =>
          exact QuarticChamberResidual810.rDG1 hc
        | cDG2 hc =>
          exact (quarticChamberDG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cEF0 hc =>
          exact QuarticChamberResidual810.rEF0 hc
        | cEF1 hc =>
          exact QuarticChamberResidual810.rEF1 hc
        | cEF2 hc =>
          exact (quarticChamberEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cEG0 hc =>
          exact QuarticChamberResidual810.rEG0 hc
        | cEG1 hc =>
          exact QuarticChamberResidual810.rEG1 hc
        | cEG2 hc =>
          exact (quarticChamberEG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cFG0 hc =>
          exact QuarticChamberResidual810.rFG0 hc
        | cFG1 hc =>
          exact QuarticChamberResidual810.rFG1 hc
        | cFG2 hc =>
          exact (quarticChamberFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
      | size3 h =>
        cases h with
        | cBCD0 hc =>
          exact QuarticChamberResidual810.rBCD0 hc
        | cBCD1 hc =>
          exact QuarticChamberResidual810.rBCD1 hc
        | cBCD2 hc =>
          exact (quarticChamberBCD2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCD3 hc =>
          exact (quarticChamberBCD3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCD4 hc =>
          exact QuarticChamberResidual810.rBCD4 hc
        | cBCD5 hc =>
          exact QuarticChamberResidual810.rBCD5 hc
        | cBCD6 hc =>
          exact QuarticChamberResidual810.rBCD6 hc
        | cBCE0 hc =>
          exact QuarticChamberResidual810.rBCE0 hc
        | cBCE1 hc =>
          exact QuarticChamberResidual810.rBCE1 hc
        | cBCE2 hc =>
          exact (quarticChamberBCE2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCE3 hc =>
          exact (quarticChamberBCE3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCE4 hc =>
          exact QuarticChamberResidual810.rBCE4 hc
        | cBCE5 hc =>
          exact QuarticChamberResidual810.rBCE5 hc
        | cBCE6 hc =>
          exact QuarticChamberResidual810.rBCE6 hc
        | cBCF0 hc =>
          exact QuarticChamberResidual810.rBCF0 hc
        | cBCF1 hc =>
          exact QuarticChamberResidual810.rBCF1 hc
        | cBCF2 hc =>
          exact (quarticChamberBCF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF3 hc =>
          exact QuarticChamberResidual810.rBCF3 hc
        | cBCF4 hc =>
          exact (quarticChamberBCF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF5 hc =>
          exact QuarticChamberResidual810.rBCF5 hc
        | cBCF6 hc =>
          exact (quarticChamberBCF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF7 hc =>
          exact (quarticChamberBCF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF8 hc =>
          exact (quarticChamberBCF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF9 hc =>
          exact QuarticChamberResidual810.rBCF9 hc
        | cBCF10 hc =>
          exact (quarticChamberBCF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF11 hc =>
          exact (quarticChamberBCF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCF12 hc =>
          exact (quarticChamberBCF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCG0 hc =>
          exact QuarticChamberResidual810.rBCG0 hc
        | cBCG1 hc =>
          exact QuarticChamberResidual810.rBCG1 hc
        | cBCG2 hc =>
          exact QuarticChamberResidual810.rBCG2 hc
        | cBCG3 hc =>
          exact QuarticChamberResidual810.rBCG3 hc
        | cBCG4 hc =>
          exact (quarticChamberBCG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG5 hc =>
          exact QuarticChamberResidual810.rBCG5 hc
        | cBCG6 hc =>
          exact (quarticChamberBCG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG7 hc =>
          exact (quarticChamberBCG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCG8 hc =>
          exact (quarticChamberBCG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG9 hc =>
          exact (quarticChamberBCG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG10 hc =>
          exact QuarticChamberResidual810.rBCG10 hc
        | cBCG11 hc =>
          exact (quarticChamberBCG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG12 hc =>
          exact (quarticChamberBCG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDE0 hc =>
          exact QuarticChamberResidual810.rBDE0 hc
        | cBDE1 hc =>
          exact (quarticChamberBDE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDE2 hc =>
          exact QuarticChamberResidual810.rBDE2 hc
        | cBDE3 hc =>
          exact QuarticChamberResidual810.rBDE3 hc
        | cBDE4 hc =>
          exact QuarticChamberResidual810.rBDE4 hc
        | cBDE5 hc =>
          exact (quarticChamberBDE5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDE6 hc =>
          exact QuarticChamberResidual810.rBDE6 hc
        | cBDF0 hc =>
          exact QuarticChamberResidual810.rBDF0 hc
        | cBDF1 hc =>
          exact (quarticChamberBDF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF2 hc =>
          exact QuarticChamberResidual810.rBDF2 hc
        | cBDF3 hc =>
          exact QuarticChamberResidual810.rBDF3 hc
        | cBDF4 hc =>
          exact QuarticChamberResidual810.rBDF4 hc
        | cBDF5 hc =>
          exact (quarticChamberBDF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDF6 hc =>
          exact (quarticChamberBDF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF7 hc =>
          exact (quarticChamberBDF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF8 hc =>
          exact QuarticChamberResidual810.rBDF8 hc
        | cBDF9 hc =>
          exact QuarticChamberResidual810.rBDF9 hc
        | cBDF10 hc =>
          exact (quarticChamberBDF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDG0 hc =>
          exact QuarticChamberResidual810.rBDG0 hc
        | cBDG1 hc =>
          exact QuarticChamberResidual810.rBDG1 hc
        | cBDG2 hc =>
          exact QuarticChamberResidual810.rBDG2 hc
        | cBDG3 hc =>
          exact (quarticChamberBDG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG4 hc =>
          exact QuarticChamberResidual810.rBDG4 hc
        | cBDG5 hc =>
          exact (quarticChamberBDG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG6 hc =>
          exact (quarticChamberBDG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDG7 hc =>
          exact (quarticChamberBDG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG8 hc =>
          exact QuarticChamberResidual810.rBDG8 hc
        | cBDG9 hc =>
          exact (quarticChamberBDG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG10 hc =>
          exact (quarticChamberBDG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEF0 hc =>
          exact QuarticChamberResidual810.rBEF0 hc
        | cBEF1 hc =>
          exact (quarticChamberBEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF2 hc =>
          exact QuarticChamberResidual810.rBEF2 hc
        | cBEF3 hc =>
          exact QuarticChamberResidual810.rBEF3 hc
        | cBEF4 hc =>
          exact QuarticChamberResidual810.rBEF4 hc
        | cBEF5 hc =>
          exact (quarticChamberBEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEF6 hc =>
          exact (quarticChamberBEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF7 hc =>
          exact (quarticChamberBEF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF8 hc =>
          exact QuarticChamberResidual810.rBEF8 hc
        | cBEF9 hc =>
          exact (quarticChamberBEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF10 hc =>
          exact (quarticChamberBEF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEG0 hc =>
          exact QuarticChamberResidual810.rBEG0 hc
        | cBEG1 hc =>
          exact QuarticChamberResidual810.rBEG1 hc
        | cBEG2 hc =>
          exact QuarticChamberResidual810.rBEG2 hc
        | cBEG3 hc =>
          exact (quarticChamberBEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG4 hc =>
          exact QuarticChamberResidual810.rBEG4 hc
        | cBEG5 hc =>
          exact (quarticChamberBEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG6 hc =>
          exact (quarticChamberBEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEG7 hc =>
          exact (quarticChamberBEG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG8 hc =>
          exact QuarticChamberResidual810.rBEG8 hc
        | cBEG9 hc =>
          exact (quarticChamberBEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG10 hc =>
          exact (quarticChamberBEG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBFG0 hc =>
          exact QuarticChamberResidual810.rBFG0 hc
        | cBFG1 hc =>
          exact (quarticChamberBFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG2 hc =>
          exact QuarticChamberResidual810.rBFG2 hc
        | cBFG3 hc =>
          exact (quarticChamberBFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG4 hc =>
          exact QuarticChamberResidual810.rBFG4 hc
        | cBFG5 hc =>
          exact (quarticChamberBFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG6 hc =>
          exact (quarticChamberBFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG7 hc =>
          exact QuarticChamberResidual810.rBFG7 hc
        | cBFG8 hc =>
          exact QuarticChamberResidual810.rBFG8 hc
        | cBFG9 hc =>
          exact (quarticChamberBFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBFG10 hc =>
          exact (quarticChamberBFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBFG11 hc =>
          exact (quarticChamberBFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBFG12 hc =>
          exact (quarticChamberBFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDE0 hc =>
          exact (quarticChamberCDE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDE1 hc =>
          exact (quarticChamberCDE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDE2 hc =>
          exact QuarticChamberResidual810.rCDE2 hc
        | cCDE3 hc =>
          exact QuarticChamberResidual810.rCDE3 hc
        | cCDE4 hc =>
          exact QuarticChamberResidual810.rCDE4 hc
        | cCDE5 hc =>
          exact (quarticChamberCDE5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDE6 hc =>
          exact QuarticChamberResidual810.rCDE6 hc
        | cCDF0 hc =>
          exact (quarticChamberCDF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDF1 hc =>
          exact QuarticChamberResidual810.rCDF1 hc
        | cCDF2 hc =>
          exact (quarticChamberCDF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDF3 hc =>
          exact (quarticChamberCDF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDF4 hc =>
          exact QuarticChamberResidual810.rCDF4 hc
        | cCDF5 hc =>
          exact QuarticChamberResidual810.rCDF5 hc
        | cCDF6 hc =>
          exact (quarticChamberCDF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDF7 hc =>
          exact (quarticChamberCDF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDF8 hc =>
          exact QuarticChamberResidual810.rCDF8 hc
        | cCDF9 hc =>
          exact QuarticChamberResidual810.rCDF9 hc
        | cCDF10 hc =>
          exact (quarticChamberCDF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDG0 hc =>
          exact (quarticChamberCDG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDG1 hc =>
          exact QuarticChamberResidual810.rCDG1 hc
        | cCDG2 hc =>
          exact QuarticChamberResidual810.rCDG2 hc
        | cCDG3 hc =>
          exact QuarticChamberResidual810.rCDG3 hc
        | cCDG4 hc =>
          exact QuarticChamberResidual810.rCDG4 hc
        | cCDG5 hc =>
          exact (quarticChamberCDG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDG6 hc =>
          exact QuarticChamberResidual810.rCDG6 hc
        | cCDG7 hc =>
          exact (quarticChamberCDG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDG8 hc =>
          exact QuarticChamberResidual810.rCDG8 hc
        | cCDG9 hc =>
          exact (quarticChamberCDG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDG10 hc =>
          exact (quarticChamberCDG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCEF0 hc =>
          exact (quarticChamberCEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF1 hc =>
          exact QuarticChamberResidual810.rCEF1 hc
        | cCEF2 hc =>
          exact (quarticChamberCEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF3 hc =>
          exact (quarticChamberCEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF4 hc =>
          exact QuarticChamberResidual810.rCEF4 hc
        | cCEF5 hc =>
          exact (quarticChamberCEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF6 hc =>
          exact (quarticChamberCEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEF7 hc =>
          exact (quarticChamberCEF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF8 hc =>
          exact QuarticChamberResidual810.rCEF8 hc
        | cCEF9 hc =>
          exact (quarticChamberCEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF10 hc =>
          exact (quarticChamberCEF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEG0 hc =>
          exact (quarticChamberCEG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEG1 hc =>
          exact QuarticChamberResidual810.rCEG1 hc
        | cCEG2 hc =>
          exact QuarticChamberResidual810.rCEG2 hc
        | cCEG3 hc =>
          exact (quarticChamberCEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEG4 hc =>
          exact QuarticChamberResidual810.rCEG4 hc
        | cCEG5 hc =>
          exact (quarticChamberCEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEG6 hc =>
          exact QuarticChamberResidual810.rCEG6 hc
        | cCEG7 hc =>
          exact (quarticChamberCEG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEG8 hc =>
          exact (quarticChamberCEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEG9 hc =>
          exact (quarticChamberCEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEG10 hc =>
          exact (quarticChamberCEG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCFG0 hc =>
          exact (quarticChamberCFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCFG1 hc =>
          exact QuarticChamberResidual810.rCFG1 hc
        | cCFG2 hc =>
          exact (quarticChamberCFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCFG3 hc =>
          exact QuarticChamberResidual810.rCFG3 hc
        | cCFG4 hc =>
          exact QuarticChamberResidual810.rCFG4 hc
        | cCFG5 hc =>
          exact QuarticChamberResidual810.rCFG5 hc
        | cCFG6 hc =>
          exact (quarticChamberCFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCFG7 hc =>
          exact QuarticChamberResidual810.rCFG7 hc
        | cCFG8 hc =>
          exact QuarticChamberResidual810.rCFG8 hc
        | cCFG9 hc =>
          exact QuarticChamberResidual810.rCFG9 hc
        | cCFG10 hc =>
          exact (quarticChamberCFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCFG11 hc =>
          exact (quarticChamberCFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCFG12 hc =>
          exact (quarticChamberCFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEF0 hc =>
          exact (quarticChamberDEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDEF1 hc =>
          exact (quarticChamberDEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEF2 hc =>
          exact QuarticChamberResidual810.rDEF2 hc
        | cDEF3 hc =>
          exact QuarticChamberResidual810.rDEF3 hc
        | cDEF4 hc =>
          exact (quarticChamberDEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDEF5 hc =>
          exact (quarticChamberDEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDEF6 hc =>
          exact (quarticChamberDEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEG0 hc =>
          exact QuarticChamberResidual810.rDEG0 hc
        | cDEG1 hc =>
          exact (quarticChamberDEG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEG2 hc =>
          exact QuarticChamberResidual810.rDEG2 hc
        | cDEG3 hc =>
          exact QuarticChamberResidual810.rDEG3 hc
        | cDEG4 hc =>
          exact QuarticChamberResidual810.rDEG4 hc
        | cDEG5 hc =>
          exact QuarticChamberResidual810.rDEG5 hc
        | cDEG6 hc =>
          exact (quarticChamberDEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDFG0 hc =>
          exact QuarticChamberResidual810.rDFG0 hc
        | cDFG1 hc =>
          exact QuarticChamberResidual810.rDFG1 hc
        | cDFG2 hc =>
          exact QuarticChamberResidual810.rDFG2 hc
        | cDFG3 hc =>
          exact QuarticChamberResidual810.rDFG3 hc
        | cDFG4 hc =>
          exact (quarticChamberDFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDFG5 hc =>
          exact (quarticChamberDFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDFG6 hc =>
          exact (quarticChamberDFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cEFG0 hc =>
          exact QuarticChamberResidual810.rEFG0 hc
        | cEFG1 hc =>
          exact QuarticChamberResidual810.rEFG1 hc
        | cEFG2 hc =>
          exact QuarticChamberResidual810.rEFG2 hc
        | cEFG3 hc =>
          exact QuarticChamberResidual810.rEFG3 hc
        | cEFG4 hc =>
          exact (quarticChamberEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cEFG5 hc =>
          exact (quarticChamberEFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cEFG6 hc =>
          exact (quarticChamberEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
      | size4 h =>
        cases h with
        | cBCDE0 hc =>
          exact QuarticChamberResidual810.rBCDE0 hc
        | cBCDE1 hc =>
          exact QuarticChamberResidual810.rBCDE1 hc
        | cBCDE2 hc =>
          exact (quarticChamberBCDE2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDE3 hc =>
          exact (quarticChamberBCDE3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDE4 hc =>
          exact QuarticChamberResidual810.rBCDE4 hc
        | cBCDE5 hc =>
          exact QuarticChamberResidual810.rBCDE5 hc
        | cBCDE6 hc =>
          exact QuarticChamberResidual810.rBCDE6 hc
        | cBCDE7 hc =>
          exact QuarticChamberResidual810.rBCDE7 hc
        | cBCDE8 hc =>
          exact QuarticChamberResidual810.rBCDE8 hc
        | cBCDE9 hc =>
          exact QuarticChamberResidual810.rBCDE9 hc
        | cBCDE10 hc =>
          exact QuarticChamberResidual810.rBCDE10 hc
        | cBCDE11 hc =>
          exact (quarticChamberBCDE11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDE12 hc =>
          exact QuarticChamberResidual810.rBCDE12 hc
        | cBCDE13 hc =>
          exact QuarticChamberResidual810.rBCDE13 hc
        | cBCDE14 hc =>
          exact (quarticChamberBCDE14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDF0 hc =>
          exact QuarticChamberResidual810.rBCDF0 hc
        | cBCDF1 hc =>
          exact QuarticChamberResidual810.rBCDF1 hc
        | cBCDF2 hc =>
          exact (quarticChamberBCDF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF3 hc =>
          exact QuarticChamberResidual810.rBCDF3 hc
        | cBCDF4 hc =>
          exact (quarticChamberBCDF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF5 hc =>
          exact QuarticChamberResidual810.rBCDF5 hc
        | cBCDF6 hc =>
          exact QuarticChamberResidual810.rBCDF6 hc
        | cBCDF7 hc =>
          exact QuarticChamberResidual810.rBCDF7 hc
        | cBCDF8 hc =>
          exact (quarticChamberBCDF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDF9 hc =>
          exact (quarticChamberBCDF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF10 hc =>
          exact (quarticChamberBCDF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDF11 hc =>
          exact QuarticChamberResidual810.rBCDF11 hc
        | cBCDF12 hc =>
          exact (quarticChamberBCDF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDF13 hc =>
          exact (quarticChamberBCDF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF14 hc =>
          exact (quarticChamberBCDF14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF15 hc =>
          exact QuarticChamberResidual810.rBCDF15 hc
        | cBCDF16 hc =>
          exact (quarticChamberBCDF16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF17 hc =>
          exact (quarticChamberBCDF17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF18 hc =>
          exact QuarticChamberResidual810.rBCDF18 hc
        | cBCDF19 hc =>
          exact QuarticChamberResidual810.rBCDF19 hc
        | cBCDF20 hc =>
          exact (quarticChamberBCDF20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDF21 hc =>
          exact (quarticChamberBCDF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF22 hc =>
          exact QuarticChamberResidual810.rBCDF22 hc
        | cBCDF23 hc =>
          exact QuarticChamberResidual810.rBCDF23 hc
        | cBCDF24 hc =>
          exact QuarticChamberResidual810.rBCDF24 hc
        | cBCDF25 hc =>
          exact QuarticChamberResidual810.rBCDF25 hc
        | cBCDF26 hc =>
          exact (quarticChamberBCDF26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDG0 hc =>
          exact QuarticChamberResidual810.rBCDG0 hc
        | cBCDG1 hc =>
          exact QuarticChamberResidual810.rBCDG1 hc
        | cBCDG2 hc =>
          exact QuarticChamberResidual810.rBCDG2 hc
        | cBCDG3 hc =>
          exact QuarticChamberResidual810.rBCDG3 hc
        | cBCDG4 hc =>
          exact (quarticChamberBCDG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG5 hc =>
          exact QuarticChamberResidual810.rBCDG5 hc
        | cBCDG6 hc =>
          exact QuarticChamberResidual810.rBCDG6 hc
        | cBCDG7 hc =>
          exact QuarticChamberResidual810.rBCDG7 hc
        | cBCDG8 hc =>
          exact (quarticChamberBCDG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDG9 hc =>
          exact (quarticChamberBCDG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG10 hc =>
          exact (quarticChamberBCDG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG11 hc =>
          exact QuarticChamberResidual810.rBCDG11 hc
        | cBCDG12 hc =>
          exact (quarticChamberBCDG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG13 hc =>
          exact (quarticChamberBCDG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDG14 hc =>
          exact (quarticChamberBCDG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG15 hc =>
          exact (quarticChamberBCDG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG16 hc =>
          exact QuarticChamberResidual810.rBCDG16 hc
        | cBCDG17 hc =>
          exact QuarticChamberResidual810.rBCDG17 hc
        | cBCDG18 hc =>
          exact QuarticChamberResidual810.rBCDG18 hc
        | cBCDG19 hc =>
          exact (quarticChamberBCDG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDG20 hc =>
          exact (quarticChamberBCDG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG21 hc =>
          exact (quarticChamberBCDG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG22 hc =>
          exact QuarticChamberResidual810.rBCDG22 hc
        | cBCDG23 hc =>
          exact QuarticChamberResidual810.rBCDG23 hc
        | cBCDG24 hc =>
          exact QuarticChamberResidual810.rBCDG24 hc
        | cBCDG25 hc =>
          exact (quarticChamberBCDG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG26 hc =>
          exact (quarticChamberBCDG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEF0 hc =>
          exact QuarticChamberResidual810.rBCEF0 hc
        | cBCEF1 hc =>
          exact QuarticChamberResidual810.rBCEF1 hc
        | cBCEF2 hc =>
          exact (quarticChamberBCEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF3 hc =>
          exact QuarticChamberResidual810.rBCEF3 hc
        | cBCEF4 hc =>
          exact (quarticChamberBCEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF5 hc =>
          exact QuarticChamberResidual810.rBCEF5 hc
        | cBCEF6 hc =>
          exact QuarticChamberResidual810.rBCEF6 hc
        | cBCEF7 hc =>
          exact QuarticChamberResidual810.rBCEF7 hc
        | cBCEF8 hc =>
          exact (quarticChamberBCEF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEF9 hc =>
          exact (quarticChamberBCEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF10 hc =>
          exact (quarticChamberBCEF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEF11 hc =>
          exact QuarticChamberResidual810.rBCEF11 hc
        | cBCEF12 hc =>
          exact (quarticChamberBCEF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEF13 hc =>
          exact (quarticChamberBCEF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF14 hc =>
          exact (quarticChamberBCEF14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF15 hc =>
          exact QuarticChamberResidual810.rBCEF15 hc
        | cBCEF16 hc =>
          exact (quarticChamberBCEF16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF17 hc =>
          exact (quarticChamberBCEF17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF18 hc =>
          exact QuarticChamberResidual810.rBCEF18 hc
        | cBCEF19 hc =>
          exact (quarticChamberBCEF19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF20 hc =>
          exact (quarticChamberBCEF20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEF21 hc =>
          exact (quarticChamberBCEF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF22 hc =>
          exact QuarticChamberResidual810.rBCEF22 hc
        | cBCEF23 hc =>
          exact QuarticChamberResidual810.rBCEF23 hc
        | cBCEF24 hc =>
          exact (quarticChamberBCEF24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEF25 hc =>
          exact (quarticChamberBCEF25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF26 hc =>
          exact (quarticChamberBCEF26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEG0 hc =>
          exact QuarticChamberResidual810.rBCEG0 hc
        | cBCEG1 hc =>
          exact QuarticChamberResidual810.rBCEG1 hc
        | cBCEG2 hc =>
          exact QuarticChamberResidual810.rBCEG2 hc
        | cBCEG3 hc =>
          exact QuarticChamberResidual810.rBCEG3 hc
        | cBCEG4 hc =>
          exact (quarticChamberBCEG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG5 hc =>
          exact QuarticChamberResidual810.rBCEG5 hc
        | cBCEG6 hc =>
          exact QuarticChamberResidual810.rBCEG6 hc
        | cBCEG7 hc =>
          exact QuarticChamberResidual810.rBCEG7 hc
        | cBCEG8 hc =>
          exact (quarticChamberBCEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEG9 hc =>
          exact (quarticChamberBCEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG10 hc =>
          exact (quarticChamberBCEG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG11 hc =>
          exact QuarticChamberResidual810.rBCEG11 hc
        | cBCEG12 hc =>
          exact (quarticChamberBCEG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG13 hc =>
          exact (quarticChamberBCEG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEG14 hc =>
          exact (quarticChamberBCEG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG15 hc =>
          exact (quarticChamberBCEG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG16 hc =>
          exact QuarticChamberResidual810.rBCEG16 hc
        | cBCEG17 hc =>
          exact QuarticChamberResidual810.rBCEG17 hc
        | cBCEG18 hc =>
          exact QuarticChamberResidual810.rBCEG18 hc
        | cBCEG19 hc =>
          exact (quarticChamberBCEG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEG20 hc =>
          exact (quarticChamberBCEG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG21 hc =>
          exact (quarticChamberBCEG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG22 hc =>
          exact QuarticChamberResidual810.rBCEG22 hc
        | cBCEG23 hc =>
          exact QuarticChamberResidual810.rBCEG23 hc
        | cBCEG24 hc =>
          exact QuarticChamberResidual810.rBCEG24 hc
        | cBCEG25 hc =>
          exact (quarticChamberBCEG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG26 hc =>
          exact (quarticChamberBCEG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCFG0 hc =>
          exact QuarticChamberResidual810.rBCFG0 hc
        | cBCFG1 hc =>
          exact QuarticChamberResidual810.rBCFG1 hc
        | cBCFG2 hc =>
          exact (quarticChamberBCFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG3 hc =>
          exact QuarticChamberResidual810.rBCFG3 hc
        | cBCFG4 hc =>
          exact (quarticChamberBCFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG5 hc =>
          exact QuarticChamberResidual810.rBCFG5 hc
        | cBCFG6 hc =>
          exact (quarticChamberBCFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG7 hc =>
          exact QuarticChamberResidual810.rBCFG7 hc
        | cBCFG8 hc =>
          exact (quarticChamberBCFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG9 hc =>
          exact (quarticChamberBCFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG10 hc =>
          exact (quarticChamberBCFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG11 hc =>
          exact QuarticChamberResidual810.rBCFG11 hc
        | cBCFG12 hc =>
          exact (quarticChamberBCFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG13 hc =>
          exact (quarticChamberBCFG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG14 hc =>
          exact QuarticChamberResidual810.rBCFG14 hc
        | cBCFG15 hc =>
          exact QuarticChamberResidual810.rBCFG15 hc
        | cBCFG16 hc =>
          exact (quarticChamberBCFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG17 hc =>
          exact QuarticChamberResidual810.rBCFG17 hc
        | cBCFG18 hc =>
          exact (quarticChamberBCFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG19 hc =>
          exact (quarticChamberBCFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCFG20 hc =>
          exact (quarticChamberBCFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG21 hc =>
          exact QuarticChamberResidual810.rBCFG21 hc
        | cBCFG22 hc =>
          exact (quarticChamberBCFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG23 hc =>
          exact (quarticChamberBCFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG24 hc =>
          exact QuarticChamberResidual810.rBCFG24 hc
        | cBCFG25 hc =>
          exact (quarticChamberBCFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG26 hc =>
          exact (quarticChamberBCFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG27 hc =>
          exact (quarticChamberBCFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG28 hc =>
          exact QuarticChamberResidual810.rBCFG28 hc
        | cBCFG29 hc =>
          exact (quarticChamberBCFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG30 hc =>
          exact (quarticChamberBCFG30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG31 hc =>
          exact (quarticChamberBCFG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG32 hc =>
          exact (quarticChamberBCFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF0 hc =>
          exact QuarticChamberResidual810.rBDEF0 hc
        | cBDEF1 hc =>
          exact (quarticChamberBDEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF2 hc =>
          exact QuarticChamberResidual810.rBDEF2 hc
        | cBDEF3 hc =>
          exact (quarticChamberBDEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEF4 hc =>
          exact QuarticChamberResidual810.rBDEF4 hc
        | cBDEF5 hc =>
          exact (quarticChamberBDEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF6 hc =>
          exact QuarticChamberResidual810.rBDEF6 hc
        | cBDEF7 hc =>
          exact QuarticChamberResidual810.rBDEF7 hc
        | cBDEF8 hc =>
          exact (quarticChamberBDEF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF9 hc =>
          exact (quarticChamberBDEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF10 hc =>
          exact QuarticChamberResidual810.rBDEF10 hc
        | cBDEF11 hc =>
          exact (quarticChamberBDEF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEF12 hc =>
          exact (quarticChamberBDEF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF13 hc =>
          exact (quarticChamberBDEF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF14 hc =>
          exact QuarticChamberResidual810.rBDEF14 hc
        | cBDEF15 hc =>
          exact (quarticChamberBDEF15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF16 hc =>
          exact QuarticChamberResidual810.rBDEF16 hc
        | cBDEF17 hc =>
          exact QuarticChamberResidual810.rBDEF17 hc
        | cBDEF18 hc =>
          exact QuarticChamberResidual810.rBDEF18 hc
        | cBDEF19 hc =>
          exact (quarticChamberBDEF19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF20 hc =>
          exact QuarticChamberResidual810.rBDEF20 hc
        | cBDEF21 hc =>
          exact (quarticChamberBDEF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF22 hc =>
          exact (quarticChamberBDEF22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG0 hc =>
          exact QuarticChamberResidual810.rBDEG0 hc
        | cBDEG1 hc =>
          exact QuarticChamberResidual810.rBDEG1 hc
        | cBDEG2 hc =>
          exact QuarticChamberResidual810.rBDEG2 hc
        | cBDEG3 hc =>
          exact (quarticChamberBDEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG4 hc =>
          exact QuarticChamberResidual810.rBDEG4 hc
        | cBDEG5 hc =>
          exact (quarticChamberBDEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG6 hc =>
          exact (quarticChamberBDEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG7 hc =>
          exact QuarticChamberResidual810.rBDEG7 hc
        | cBDEG8 hc =>
          exact (quarticChamberBDEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG9 hc =>
          exact (quarticChamberBDEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG10 hc =>
          exact QuarticChamberResidual810.rBDEG10 hc
        | cBDEG11 hc =>
          exact (quarticChamberBDEG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG12 hc =>
          exact (quarticChamberBDEG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEG13 hc =>
          exact (quarticChamberBDEG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG14 hc =>
          exact QuarticChamberResidual810.rBDEG14 hc
        | cBDEG15 hc =>
          exact (quarticChamberBDEG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG16 hc =>
          exact QuarticChamberResidual810.rBDEG16 hc
        | cBDEG17 hc =>
          exact QuarticChamberResidual810.rBDEG17 hc
        | cBDEG18 hc =>
          exact (quarticChamberBDEG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG19 hc =>
          exact (quarticChamberBDEG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG20 hc =>
          exact QuarticChamberResidual810.rBDEG20 hc
        | cBDEG21 hc =>
          exact (quarticChamberBDEG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG22 hc =>
          exact (quarticChamberBDEG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDFG0 hc =>
          exact QuarticChamberResidual810.rBDFG0 hc
        | cBDFG1 hc =>
          exact (quarticChamberBDFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG2 hc =>
          exact QuarticChamberResidual810.rBDFG2 hc
        | cBDFG3 hc =>
          exact (quarticChamberBDFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG4 hc =>
          exact QuarticChamberResidual810.rBDFG4 hc
        | cBDFG5 hc =>
          exact QuarticChamberResidual810.rBDFG5 hc
        | cBDFG6 hc =>
          exact QuarticChamberResidual810.rBDFG6 hc
        | cBDFG7 hc =>
          exact QuarticChamberResidual810.rBDFG7 hc
        | cBDFG8 hc =>
          exact (quarticChamberBDFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG9 hc =>
          exact (quarticChamberBDFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDFG10 hc =>
          exact QuarticChamberResidual810.rBDFG10 hc
        | cBDFG11 hc =>
          exact (quarticChamberBDFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDFG12 hc =>
          exact (quarticChamberBDFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG13 hc =>
          exact QuarticChamberResidual810.rBDFG13 hc
        | cBDFG14 hc =>
          exact QuarticChamberResidual810.rBDFG14 hc
        | cBDFG15 hc =>
          exact (quarticChamberBDFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG16 hc =>
          exact QuarticChamberResidual810.rBDFG16 hc
        | cBDFG17 hc =>
          exact (quarticChamberBDFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG18 hc =>
          exact (quarticChamberBDFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDFG19 hc =>
          exact (quarticChamberBDFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG20 hc =>
          exact QuarticChamberResidual810.rBDFG20 hc
        | cBDFG21 hc =>
          exact QuarticChamberResidual810.rBDFG21 hc
        | cBDFG22 hc =>
          exact QuarticChamberResidual810.rBDFG22 hc
        | cBDFG23 hc =>
          exact (quarticChamberBDFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG24 hc =>
          exact (quarticChamberBDFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDFG25 hc =>
          exact (quarticChamberBDFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDFG26 hc =>
          exact (quarticChamberBDFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEFG0 hc =>
          exact QuarticChamberResidual810.rBEFG0 hc
        | cBEFG1 hc =>
          exact (quarticChamberBEFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG2 hc =>
          exact QuarticChamberResidual810.rBEFG2 hc
        | cBEFG3 hc =>
          exact (quarticChamberBEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG4 hc =>
          exact QuarticChamberResidual810.rBEFG4 hc
        | cBEFG5 hc =>
          exact QuarticChamberResidual810.rBEFG5 hc
        | cBEFG6 hc =>
          exact QuarticChamberResidual810.rBEFG6 hc
        | cBEFG7 hc =>
          exact QuarticChamberResidual810.rBEFG7 hc
        | cBEFG8 hc =>
          exact (quarticChamberBEFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG9 hc =>
          exact (quarticChamberBEFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEFG10 hc =>
          exact QuarticChamberResidual810.rBEFG10 hc
        | cBEFG11 hc =>
          exact (quarticChamberBEFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEFG12 hc =>
          exact (quarticChamberBEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG13 hc =>
          exact QuarticChamberResidual810.rBEFG13 hc
        | cBEFG14 hc =>
          exact QuarticChamberResidual810.rBEFG14 hc
        | cBEFG15 hc =>
          exact (quarticChamberBEFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG16 hc =>
          exact QuarticChamberResidual810.rBEFG16 hc
        | cBEFG17 hc =>
          exact (quarticChamberBEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG18 hc =>
          exact (quarticChamberBEFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEFG19 hc =>
          exact (quarticChamberBEFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG20 hc =>
          exact QuarticChamberResidual810.rBEFG20 hc
        | cBEFG21 hc =>
          exact (quarticChamberBEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG22 hc =>
          exact (quarticChamberBEFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG23 hc =>
          exact (quarticChamberBEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG24 hc =>
          exact (quarticChamberBEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEFG25 hc =>
          exact (quarticChamberBEFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEFG26 hc =>
          exact (quarticChamberBEFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEF0 hc =>
          exact (quarticChamberCDEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF1 hc =>
          exact QuarticChamberResidual810.rCDEF1 hc
        | cCDEF2 hc =>
          exact (quarticChamberCDEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF3 hc =>
          exact (quarticChamberCDEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF4 hc =>
          exact QuarticChamberResidual810.rCDEF4 hc
        | cCDEF5 hc =>
          exact (quarticChamberCDEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEF6 hc =>
          exact (quarticChamberCDEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEF7 hc =>
          exact QuarticChamberResidual810.rCDEF7 hc
        | cCDEF8 hc =>
          exact QuarticChamberResidual810.rCDEF8 hc
        | cCDEF9 hc =>
          exact (quarticChamberCDEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF10 hc =>
          exact QuarticChamberResidual810.rCDEF10 hc
        | cCDEF11 hc =>
          exact (quarticChamberCDEF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF12 hc =>
          exact (quarticChamberCDEF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEF13 hc =>
          exact (quarticChamberCDEF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF14 hc =>
          exact QuarticChamberResidual810.rCDEF14 hc
        | cCDEF15 hc =>
          exact (quarticChamberCDEF15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEF16 hc =>
          exact QuarticChamberResidual810.rCDEF16 hc
        | cCDEF17 hc =>
          exact QuarticChamberResidual810.rCDEF17 hc
        | cCDEF18 hc =>
          exact QuarticChamberResidual810.rCDEF18 hc
        | cCDEF19 hc =>
          exact (quarticChamberCDEF19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF20 hc =>
          exact (quarticChamberCDEF20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEF21 hc =>
          exact (quarticChamberCDEF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF22 hc =>
          exact (quarticChamberCDEF22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEG0 hc =>
          exact (quarticChamberCDEG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG1 hc =>
          exact QuarticChamberResidual810.rCDEG1 hc
        | cCDEG2 hc =>
          exact QuarticChamberResidual810.rCDEG2 hc
        | cCDEG3 hc =>
          exact QuarticChamberResidual810.rCDEG3 hc
        | cCDEG4 hc =>
          exact QuarticChamberResidual810.rCDEG4 hc
        | cCDEG5 hc =>
          exact (quarticChamberCDEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEG6 hc =>
          exact QuarticChamberResidual810.rCDEG6 hc
        | cCDEG7 hc =>
          exact QuarticChamberResidual810.rCDEG7 hc
        | cCDEG8 hc =>
          exact (quarticChamberCDEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEG9 hc =>
          exact QuarticChamberResidual810.rCDEG9 hc
        | cCDEG10 hc =>
          exact QuarticChamberResidual810.rCDEG10 hc
        | cCDEG11 hc =>
          exact (quarticChamberCDEG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEG12 hc =>
          exact QuarticChamberResidual810.rCDEG12 hc
        | cCDEG13 hc =>
          exact (quarticChamberCDEG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG14 hc =>
          exact QuarticChamberResidual810.rCDEG14 hc
        | cCDEG15 hc =>
          exact (quarticChamberCDEG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEG16 hc =>
          exact QuarticChamberResidual810.rCDEG16 hc
        | cCDEG17 hc =>
          exact QuarticChamberResidual810.rCDEG17 hc
        | cCDEG18 hc =>
          exact (quarticChamberCDEG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG19 hc =>
          exact (quarticChamberCDEG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG20 hc =>
          exact QuarticChamberResidual810.rCDEG20 hc
        | cCDEG21 hc =>
          exact (quarticChamberCDEG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG22 hc =>
          exact (quarticChamberCDEG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDFG0 hc =>
          exact (quarticChamberCDFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG1 hc =>
          exact QuarticChamberResidual810.rCDFG1 hc
        | cCDFG2 hc =>
          exact (quarticChamberCDFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG3 hc =>
          exact QuarticChamberResidual810.rCDFG3 hc
        | cCDFG4 hc =>
          exact QuarticChamberResidual810.rCDFG4 hc
        | cCDFG5 hc =>
          exact QuarticChamberResidual810.rCDFG5 hc
        | cCDFG6 hc =>
          exact QuarticChamberResidual810.rCDFG6 hc
        | cCDFG7 hc =>
          exact QuarticChamberResidual810.rCDFG7 hc
        | cCDFG8 hc =>
          exact QuarticChamberResidual810.rCDFG8 hc
        | cCDFG9 hc =>
          exact (quarticChamberCDFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG10 hc =>
          exact QuarticChamberResidual810.rCDFG10 hc
        | cCDFG11 hc =>
          exact QuarticChamberResidual810.rCDFG11 hc
        | cCDFG12 hc =>
          exact (quarticChamberCDFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDFG13 hc =>
          exact QuarticChamberResidual810.rCDFG13 hc
        | cCDFG14 hc =>
          exact QuarticChamberResidual810.rCDFG14 hc
        | cCDFG15 hc =>
          exact QuarticChamberResidual810.rCDFG15 hc
        | cCDFG16 hc =>
          exact QuarticChamberResidual810.rCDFG16 hc
        | cCDFG17 hc =>
          exact (quarticChamberCDFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDFG18 hc =>
          exact QuarticChamberResidual810.rCDFG18 hc
        | cCDFG19 hc =>
          exact (quarticChamberCDFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG20 hc =>
          exact QuarticChamberResidual810.rCDFG20 hc
        | cCDFG21 hc =>
          exact QuarticChamberResidual810.rCDFG21 hc
        | cCDFG22 hc =>
          exact QuarticChamberResidual810.rCDFG22 hc
        | cCDFG23 hc =>
          exact (quarticChamberCDFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG24 hc =>
          exact (quarticChamberCDFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDFG25 hc =>
          exact (quarticChamberCDFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDFG26 hc =>
          exact (quarticChamberCDFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCEFG0 hc =>
          exact (quarticChamberCEFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG1 hc =>
          exact QuarticChamberResidual810.rCEFG1 hc
        | cCEFG2 hc =>
          exact (quarticChamberCEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG3 hc =>
          exact QuarticChamberResidual810.rCEFG3 hc
        | cCEFG4 hc =>
          exact QuarticChamberResidual810.rCEFG4 hc
        | cCEFG5 hc =>
          exact QuarticChamberResidual810.rCEFG5 hc
        | cCEFG6 hc =>
          exact QuarticChamberResidual810.rCEFG6 hc
        | cCEFG7 hc =>
          exact QuarticChamberResidual810.rCEFG7 hc
        | cCEFG8 hc =>
          exact QuarticChamberResidual810.rCEFG8 hc
        | cCEFG9 hc =>
          exact (quarticChamberCEFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG10 hc =>
          exact QuarticChamberResidual810.rCEFG10 hc
        | cCEFG11 hc =>
          exact (quarticChamberCEFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG12 hc =>
          exact (quarticChamberCEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG13 hc =>
          exact QuarticChamberResidual810.rCEFG13 hc
        | cCEFG14 hc =>
          exact QuarticChamberResidual810.rCEFG14 hc
        | cCEFG15 hc =>
          exact QuarticChamberResidual810.rCEFG15 hc
        | cCEFG16 hc =>
          exact QuarticChamberResidual810.rCEFG16 hc
        | cCEFG17 hc =>
          exact (quarticChamberCEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG18 hc =>
          exact QuarticChamberResidual810.rCEFG18 hc
        | cCEFG19 hc =>
          exact (quarticChamberCEFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG20 hc =>
          exact QuarticChamberResidual810.rCEFG20 hc
        | cCEFG21 hc =>
          exact (quarticChamberCEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG22 hc =>
          exact (quarticChamberCEFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG23 hc =>
          exact (quarticChamberCEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG24 hc =>
          exact (quarticChamberCEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG25 hc =>
          exact (quarticChamberCEFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG26 hc =>
          exact (quarticChamberCEFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEFG0 hc =>
          exact QuarticChamberResidual810.rDEFG0 hc
        | cDEFG1 hc =>
          exact QuarticChamberResidual810.rDEFG1 hc
        | cDEFG2 hc =>
          exact (quarticChamberDEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEFG3 hc =>
          exact (quarticChamberDEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEFG4 hc =>
          exact QuarticChamberResidual810.rDEFG4 hc
        | cDEFG5 hc =>
          exact QuarticChamberResidual810.rDEFG5 hc
        | cDEFG6 hc =>
          exact QuarticChamberResidual810.rDEFG6 hc
        | cDEFG7 hc =>
          exact QuarticChamberResidual810.rDEFG7 hc
        | cDEFG8 hc =>
          exact QuarticChamberResidual810.rDEFG8 hc
        | cDEFG9 hc =>
          exact QuarticChamberResidual810.rDEFG9 hc
        | cDEFG10 hc =>
          exact QuarticChamberResidual810.rDEFG10 hc
        | cDEFG11 hc =>
          exact QuarticChamberResidual810.rDEFG11 hc
        | cDEFG12 hc =>
          exact (quarticChamberDEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEFG13 hc =>
          exact (quarticChamberDEFG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEFG14 hc =>
          exact (quarticChamberDEFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
      | size5 h =>
        cases h with
        | cBCDEF0 hc =>
          exact QuarticChamberResidual810.rBCDEF0 hc
        | cBCDEF1 hc =>
          exact QuarticChamberResidual810.rBCDEF1 hc
        | cBCDEF2 hc =>
          exact (quarticChamberBCDEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF3 hc =>
          exact QuarticChamberResidual810.rBCDEF3 hc
        | cBCDEF4 hc =>
          exact (quarticChamberBCDEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF5 hc =>
          exact QuarticChamberResidual810.rBCDEF5 hc
        | cBCDEF6 hc =>
          exact QuarticChamberResidual810.rBCDEF6 hc
        | cBCDEF7 hc =>
          exact QuarticChamberResidual810.rBCDEF7 hc
        | cBCDEF8 hc =>
          exact (quarticChamberBCDEF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF9 hc =>
          exact (quarticChamberBCDEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF10 hc =>
          exact QuarticChamberResidual810.rBCDEF10 hc
        | cBCDEF11 hc =>
          exact (quarticChamberBCDEF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF12 hc =>
          exact QuarticChamberResidual810.rBCDEF12 hc
        | cBCDEF13 hc =>
          exact QuarticChamberResidual810.rBCDEF13 hc
        | cBCDEF14 hc =>
          exact (quarticChamberBCDEF14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF15 hc =>
          exact (quarticChamberBCDEF15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF16 hc =>
          exact (quarticChamberBCDEF16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF17 hc =>
          exact QuarticChamberResidual810.rBCDEF17 hc
        | cBCDEF18 hc =>
          exact (quarticChamberBCDEF18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF19 hc =>
          exact QuarticChamberResidual810.rBCDEF19 hc
        | cBCDEF20 hc =>
          exact QuarticChamberResidual810.rBCDEF20 hc
        | cBCDEF21 hc =>
          exact (quarticChamberBCDEF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF22 hc =>
          exact (quarticChamberBCDEF22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF23 hc =>
          exact QuarticChamberResidual810.rBCDEF23 hc
        | cBCDEF24 hc =>
          exact (quarticChamberBCDEF24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF25 hc =>
          exact (quarticChamberBCDEF25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF26 hc =>
          exact (quarticChamberBCDEF26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF27 hc =>
          exact QuarticChamberResidual810.rBCDEF27 hc
        | cBCDEF28 hc =>
          exact (quarticChamberBCDEF28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF29 hc =>
          exact (quarticChamberBCDEF29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF30 hc =>
          exact QuarticChamberResidual810.rBCDEF30 hc
        | cBCDEF31 hc =>
          exact (quarticChamberBCDEF31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF32 hc =>
          exact (quarticChamberBCDEF32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF33 hc =>
          exact QuarticChamberResidual810.rBCDEF33 hc
        | cBCDEF34 hc =>
          exact QuarticChamberResidual810.rBCDEF34 hc
        | cBCDEF35 hc =>
          exact (quarticChamberBCDEF35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF36 hc =>
          exact QuarticChamberResidual810.rBCDEF36 hc
        | cBCDEF37 hc =>
          exact (quarticChamberBCDEF37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF38 hc =>
          exact (quarticChamberBCDEF38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF39 hc =>
          exact (quarticChamberBCDEF39810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF40 hc =>
          exact QuarticChamberResidual810.rBCDEF40 hc
        | cBCDEF41 hc =>
          exact QuarticChamberResidual810.rBCDEF41 hc
        | cBCDEF42 hc =>
          exact QuarticChamberResidual810.rBCDEF42 hc
        | cBCDEF43 hc =>
          exact (quarticChamberBCDEF43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF44 hc =>
          exact QuarticChamberResidual810.rBCDEF44 hc
        | cBCDEF45 hc =>
          exact QuarticChamberResidual810.rBCDEF45 hc
        | cBCDEF46 hc =>
          exact QuarticChamberResidual810.rBCDEF46 hc
        | cBCDEF47 hc =>
          exact QuarticChamberResidual810.rBCDEF47 hc
        | cBCDEF48 hc =>
          exact QuarticChamberResidual810.rBCDEF48 hc
        | cBCDEF49 hc =>
          exact (quarticChamberBCDEF49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF50 hc =>
          exact QuarticChamberResidual810.rBCDEF50 hc
        | cBCDEF51 hc =>
          exact QuarticChamberResidual810.rBCDEF51 hc
        | cBCDEF52 hc =>
          exact (quarticChamberBCDEF52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF53 hc =>
          exact (quarticChamberBCDEF53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF54 hc =>
          exact (quarticChamberBCDEF54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG0 hc =>
          exact QuarticChamberResidual810.rBCDEG0 hc
        | cBCDEG1 hc =>
          exact QuarticChamberResidual810.rBCDEG1 hc
        | cBCDEG2 hc =>
          exact QuarticChamberResidual810.rBCDEG2 hc
        | cBCDEG3 hc =>
          exact QuarticChamberResidual810.rBCDEG3 hc
        | cBCDEG4 hc =>
          exact (quarticChamberBCDEG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG5 hc =>
          exact QuarticChamberResidual810.rBCDEG5 hc
        | cBCDEG6 hc =>
          exact QuarticChamberResidual810.rBCDEG6 hc
        | cBCDEG7 hc =>
          exact QuarticChamberResidual810.rBCDEG7 hc
        | cBCDEG8 hc =>
          exact (quarticChamberBCDEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG9 hc =>
          exact (quarticChamberBCDEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG10 hc =>
          exact QuarticChamberResidual810.rBCDEG10 hc
        | cBCDEG11 hc =>
          exact (quarticChamberBCDEG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEG12 hc =>
          exact QuarticChamberResidual810.rBCDEG12 hc
        | cBCDEG13 hc =>
          exact QuarticChamberResidual810.rBCDEG13 hc
        | cBCDEG14 hc =>
          exact (quarticChamberBCDEG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG15 hc =>
          exact (quarticChamberBCDEG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG16 hc =>
          exact (quarticChamberBCDEG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG17 hc =>
          exact QuarticChamberResidual810.rBCDEG17 hc
        | cBCDEG18 hc =>
          exact (quarticChamberBCDEG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG19 hc =>
          exact (quarticChamberBCDEG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG20 hc =>
          exact QuarticChamberResidual810.rBCDEG20 hc
        | cBCDEG21 hc =>
          exact (quarticChamberBCDEG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG22 hc =>
          exact (quarticChamberBCDEG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG23 hc =>
          exact QuarticChamberResidual810.rBCDEG23 hc
        | cBCDEG24 hc =>
          exact (quarticChamberBCDEG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG25 hc =>
          exact (quarticChamberBCDEG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEG26 hc =>
          exact (quarticChamberBCDEG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG27 hc =>
          exact (quarticChamberBCDEG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG28 hc =>
          exact QuarticChamberResidual810.rBCDEG28 hc
        | cBCDEG29 hc =>
          exact (quarticChamberBCDEG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEG30 hc =>
          exact QuarticChamberResidual810.rBCDEG30 hc
        | cBCDEG31 hc =>
          exact (quarticChamberBCDEG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG32 hc =>
          exact QuarticChamberResidual810.rBCDEG32 hc
        | cBCDEG33 hc =>
          exact QuarticChamberResidual810.rBCDEG33 hc
        | cBCDEG34 hc =>
          exact (quarticChamberBCDEG34810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEG35 hc =>
          exact (quarticChamberBCDEG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG36 hc =>
          exact QuarticChamberResidual810.rBCDEG36 hc
        | cBCDEG37 hc =>
          exact (quarticChamberBCDEG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG38 hc =>
          exact (quarticChamberBCDEG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG39 hc =>
          exact (quarticChamberBCDEG39810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG40 hc =>
          exact QuarticChamberResidual810.rBCDEG40 hc
        | cBCDEG41 hc =>
          exact QuarticChamberResidual810.rBCDEG41 hc
        | cBCDEG42 hc =>
          exact QuarticChamberResidual810.rBCDEG42 hc
        | cBCDEG43 hc =>
          exact (quarticChamberBCDEG43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG44 hc =>
          exact QuarticChamberResidual810.rBCDEG44 hc
        | cBCDEG45 hc =>
          exact QuarticChamberResidual810.rBCDEG45 hc
        | cBCDEG46 hc =>
          exact QuarticChamberResidual810.rBCDEG46 hc
        | cBCDEG47 hc =>
          exact QuarticChamberResidual810.rBCDEG47 hc
        | cBCDEG48 hc =>
          exact (quarticChamberBCDEG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG49 hc =>
          exact (quarticChamberBCDEG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG50 hc =>
          exact QuarticChamberResidual810.rBCDEG50 hc
        | cBCDEG51 hc =>
          exact QuarticChamberResidual810.rBCDEG51 hc
        | cBCDEG52 hc =>
          exact (quarticChamberBCDEG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG53 hc =>
          exact (quarticChamberBCDEG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG54 hc =>
          exact (quarticChamberBCDEG54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG0 hc =>
          exact QuarticChamberResidual810.rBCDFG0 hc
        | cBCDFG1 hc =>
          exact QuarticChamberResidual810.rBCDFG1 hc
        | cBCDFG2 hc =>
          exact (quarticChamberBCDFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG3 hc =>
          exact QuarticChamberResidual810.rBCDFG3 hc
        | cBCDFG4 hc =>
          exact (quarticChamberBCDFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG5 hc =>
          exact QuarticChamberResidual810.rBCDFG5 hc
        | cBCDFG6 hc =>
          exact QuarticChamberResidual810.rBCDFG6 hc
        | cBCDFG7 hc =>
          exact QuarticChamberResidual810.rBCDFG7 hc
        | cBCDFG8 hc =>
          exact (quarticChamberBCDFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG9 hc =>
          exact QuarticChamberResidual810.rBCDFG9 hc
        | cBCDFG10 hc =>
          exact QuarticChamberResidual810.rBCDFG10 hc
        | cBCDFG11 hc =>
          exact (quarticChamberBCDFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG12 hc =>
          exact QuarticChamberResidual810.rBCDFG12 hc
        | cBCDFG13 hc =>
          exact QuarticChamberResidual810.rBCDFG13 hc
        | cBCDFG14 hc =>
          exact QuarticChamberResidual810.rBCDFG14 hc
        | cBCDFG15 hc =>
          exact (quarticChamberBCDFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG16 hc =>
          exact (quarticChamberBCDFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG17 hc =>
          exact QuarticChamberResidual810.rBCDFG17 hc
        | cBCDFG18 hc =>
          exact QuarticChamberResidual810.rBCDFG18 hc
        | cBCDFG19 hc =>
          exact QuarticChamberResidual810.rBCDFG19 hc
        | cBCDFG20 hc =>
          exact (quarticChamberBCDFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG21 hc =>
          exact (quarticChamberBCDFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG22 hc =>
          exact (quarticChamberBCDFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG23 hc =>
          exact QuarticChamberResidual810.rBCDFG23 hc
        | cBCDFG24 hc =>
          exact (quarticChamberBCDFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG25 hc =>
          exact (quarticChamberBCDFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG26 hc =>
          exact QuarticChamberResidual810.rBCDFG26 hc
        | cBCDFG27 hc =>
          exact QuarticChamberResidual810.rBCDFG27 hc
        | cBCDFG28 hc =>
          exact (quarticChamberBCDFG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG29 hc =>
          exact QuarticChamberResidual810.rBCDFG29 hc
        | cBCDFG30 hc =>
          exact QuarticChamberResidual810.rBCDFG30 hc
        | cBCDFG31 hc =>
          exact QuarticChamberResidual810.rBCDFG31 hc
        | cBCDFG32 hc =>
          exact (quarticChamberBCDFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG33 hc =>
          exact (quarticChamberBCDFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG34 hc =>
          exact (quarticChamberBCDFG34810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG35 hc =>
          exact QuarticChamberResidual810.rBCDFG35 hc
        | cBCDFG36 hc =>
          exact (quarticChamberBCDFG36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG37 hc =>
          exact (quarticChamberBCDFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG38 hc =>
          exact (quarticChamberBCDFG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG39 hc =>
          exact QuarticChamberResidual810.rBCDFG39 hc
        | cBCDFG40 hc =>
          exact (quarticChamberBCDFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG41 hc =>
          exact (quarticChamberBCDFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG42 hc =>
          exact QuarticChamberResidual810.rBCDFG42 hc
        | cBCDFG43 hc =>
          exact QuarticChamberResidual810.rBCDFG43 hc
        | cBCDFG44 hc =>
          exact QuarticChamberResidual810.rBCDFG44 hc
        | cBCDFG45 hc =>
          exact QuarticChamberResidual810.rBCDFG45 hc
        | cBCDFG46 hc =>
          exact (quarticChamberBCDFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG47 hc =>
          exact (quarticChamberBCDFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG48 hc =>
          exact QuarticChamberResidual810.rBCDFG48 hc
        | cBCDFG49 hc =>
          exact QuarticChamberResidual810.rBCDFG49 hc
        | cBCDFG50 hc =>
          exact (quarticChamberBCDFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG51 hc =>
          exact (quarticChamberBCDFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG52 hc =>
          exact QuarticChamberResidual810.rBCDFG52 hc
        | cBCDFG53 hc =>
          exact (quarticChamberBCDFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG54 hc =>
          exact QuarticChamberResidual810.rBCDFG54 hc
        | cBCDFG55 hc =>
          exact (quarticChamberBCDFG55810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG56 hc =>
          exact (quarticChamberBCDFG56810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG57 hc =>
          exact (quarticChamberBCDFG57810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG58 hc =>
          exact QuarticChamberResidual810.rBCDFG58 hc
        | cBCDFG59 hc =>
          exact QuarticChamberResidual810.rBCDFG59 hc
        | cBCDFG60 hc =>
          exact QuarticChamberResidual810.rBCDFG60 hc
        | cBCDFG61 hc =>
          exact QuarticChamberResidual810.rBCDFG61 hc
        | cBCDFG62 hc =>
          exact QuarticChamberResidual810.rBCDFG62 hc
        | cBCDFG63 hc =>
          exact (quarticChamberBCDFG63810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG64 hc =>
          exact (quarticChamberBCDFG64810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG65 hc =>
          exact (quarticChamberBCDFG65810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG66 hc =>
          exact (quarticChamberBCDFG66810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEFG0 hc =>
          exact QuarticChamberResidual810.rBCEFG0 hc
        | cBCEFG1 hc =>
          exact QuarticChamberResidual810.rBCEFG1 hc
        | cBCEFG2 hc =>
          exact (quarticChamberBCEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG3 hc =>
          exact QuarticChamberResidual810.rBCEFG3 hc
        | cBCEFG4 hc =>
          exact (quarticChamberBCEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG5 hc =>
          exact QuarticChamberResidual810.rBCEFG5 hc
        | cBCEFG6 hc =>
          exact QuarticChamberResidual810.rBCEFG6 hc
        | cBCEFG7 hc =>
          exact QuarticChamberResidual810.rBCEFG7 hc
        | cBCEFG8 hc =>
          exact (quarticChamberBCEFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG9 hc =>
          exact QuarticChamberResidual810.rBCEFG9 hc
        | cBCEFG10 hc =>
          exact QuarticChamberResidual810.rBCEFG10 hc
        | cBCEFG11 hc =>
          exact (quarticChamberBCEFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG12 hc =>
          exact QuarticChamberResidual810.rBCEFG12 hc
        | cBCEFG13 hc =>
          exact QuarticChamberResidual810.rBCEFG13 hc
        | cBCEFG14 hc =>
          exact QuarticChamberResidual810.rBCEFG14 hc
        | cBCEFG15 hc =>
          exact (quarticChamberBCEFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG16 hc =>
          exact (quarticChamberBCEFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG17 hc =>
          exact QuarticChamberResidual810.rBCEFG17 hc
        | cBCEFG18 hc =>
          exact QuarticChamberResidual810.rBCEFG18 hc
        | cBCEFG19 hc =>
          exact QuarticChamberResidual810.rBCEFG19 hc
        | cBCEFG20 hc =>
          exact (quarticChamberBCEFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG21 hc =>
          exact (quarticChamberBCEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG22 hc =>
          exact (quarticChamberBCEFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEFG23 hc =>
          exact QuarticChamberResidual810.rBCEFG23 hc
        | cBCEFG24 hc =>
          exact (quarticChamberBCEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG25 hc =>
          exact (quarticChamberBCEFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG26 hc =>
          exact QuarticChamberResidual810.rBCEFG26 hc
        | cBCEFG27 hc =>
          exact QuarticChamberResidual810.rBCEFG27 hc
        | cBCEFG28 hc =>
          exact (quarticChamberBCEFG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG29 hc =>
          exact QuarticChamberResidual810.rBCEFG29 hc
        | cBCEFG30 hc =>
          exact QuarticChamberResidual810.rBCEFG30 hc
        | cBCEFG31 hc =>
          exact QuarticChamberResidual810.rBCEFG31 hc
        | cBCEFG32 hc =>
          exact (quarticChamberBCEFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG33 hc =>
          exact (quarticChamberBCEFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG34 hc =>
          exact (quarticChamberBCEFG34810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG35 hc =>
          exact QuarticChamberResidual810.rBCEFG35 hc
        | cBCEFG36 hc =>
          exact (quarticChamberBCEFG36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG37 hc =>
          exact (quarticChamberBCEFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEFG38 hc =>
          exact (quarticChamberBCEFG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG39 hc =>
          exact QuarticChamberResidual810.rBCEFG39 hc
        | cBCEFG40 hc =>
          exact (quarticChamberBCEFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG41 hc =>
          exact (quarticChamberBCEFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG42 hc =>
          exact QuarticChamberResidual810.rBCEFG42 hc
        | cBCEFG43 hc =>
          exact QuarticChamberResidual810.rBCEFG43 hc
        | cBCEFG44 hc =>
          exact QuarticChamberResidual810.rBCEFG44 hc
        | cBCEFG45 hc =>
          exact QuarticChamberResidual810.rBCEFG45 hc
        | cBCEFG46 hc =>
          exact (quarticChamberBCEFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG47 hc =>
          exact (quarticChamberBCEFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG48 hc =>
          exact QuarticChamberResidual810.rBCEFG48 hc
        | cBCEFG49 hc =>
          exact (quarticChamberBCEFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG50 hc =>
          exact (quarticChamberBCEFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG51 hc =>
          exact (quarticChamberBCEFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG52 hc =>
          exact QuarticChamberResidual810.rBCEFG52 hc
        | cBCEFG53 hc =>
          exact (quarticChamberBCEFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG54 hc =>
          exact QuarticChamberResidual810.rBCEFG54 hc
        | cBCEFG55 hc =>
          exact (quarticChamberBCEFG55810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG56 hc =>
          exact (quarticChamberBCEFG56810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG57 hc =>
          exact (quarticChamberBCEFG57810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG58 hc =>
          exact QuarticChamberResidual810.rBCEFG58 hc
        | cBCEFG59 hc =>
          exact QuarticChamberResidual810.rBCEFG59 hc
        | cBCEFG60 hc =>
          exact (quarticChamberBCEFG60810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG61 hc =>
          exact (quarticChamberBCEFG61810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG62 hc =>
          exact (quarticChamberBCEFG62810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG63 hc =>
          exact (quarticChamberBCEFG63810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG64 hc =>
          exact (quarticChamberBCEFG64810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG65 hc =>
          exact (quarticChamberBCEFG65810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG66 hc =>
          exact (quarticChamberBCEFG66810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG0 hc =>
          exact QuarticChamberResidual810.rBDEFG0 hc
        | cBDEFG1 hc =>
          exact (quarticChamberBDEFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG2 hc =>
          exact QuarticChamberResidual810.rBDEFG2 hc
        | cBDEFG3 hc =>
          exact (quarticChamberBDEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG4 hc =>
          exact QuarticChamberResidual810.rBDEFG4 hc
        | cBDEFG5 hc =>
          exact QuarticChamberResidual810.rBDEFG5 hc
        | cBDEFG6 hc =>
          exact QuarticChamberResidual810.rBDEFG6 hc
        | cBDEFG7 hc =>
          exact QuarticChamberResidual810.rBDEFG7 hc
        | cBDEFG8 hc =>
          exact QuarticChamberResidual810.rBDEFG8 hc
        | cBDEFG9 hc =>
          exact QuarticChamberResidual810.rBDEFG9 hc
        | cBDEFG10 hc =>
          exact QuarticChamberResidual810.rBDEFG10 hc
        | cBDEFG11 hc =>
          exact QuarticChamberResidual810.rBDEFG11 hc
        | cBDEFG12 hc =>
          exact QuarticChamberResidual810.rBDEFG12 hc
        | cBDEFG13 hc =>
          exact QuarticChamberResidual810.rBDEFG13 hc
        | cBDEFG14 hc =>
          exact (quarticChamberBDEFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG15 hc =>
          exact (quarticChamberBDEFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG16 hc =>
          exact QuarticChamberResidual810.rBDEFG16 hc
        | cBDEFG17 hc =>
          exact (quarticChamberBDEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG18 hc =>
          exact QuarticChamberResidual810.rBDEFG18 hc
        | cBDEFG19 hc =>
          exact QuarticChamberResidual810.rBDEFG19 hc
        | cBDEFG20 hc =>
          exact (quarticChamberBDEFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG21 hc =>
          exact (quarticChamberBDEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG22 hc =>
          exact QuarticChamberResidual810.rBDEFG22 hc
        | cBDEFG23 hc =>
          exact (quarticChamberBDEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG24 hc =>
          exact (quarticChamberBDEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG25 hc =>
          exact QuarticChamberResidual810.rBDEFG25 hc
        | cBDEFG26 hc =>
          exact QuarticChamberResidual810.rBDEFG26 hc
        | cBDEFG27 hc =>
          exact (quarticChamberBDEFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG28 hc =>
          exact QuarticChamberResidual810.rBDEFG28 hc
        | cBDEFG29 hc =>
          exact (quarticChamberBDEFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG30 hc =>
          exact (quarticChamberBDEFG30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG31 hc =>
          exact QuarticChamberResidual810.rBDEFG31 hc
        | cBDEFG32 hc =>
          exact (quarticChamberBDEFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG33 hc =>
          exact (quarticChamberBDEFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG34 hc =>
          exact QuarticChamberResidual810.rBDEFG34 hc
        | cBDEFG35 hc =>
          exact (quarticChamberBDEFG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG36 hc =>
          exact (quarticChamberBDEFG36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG37 hc =>
          exact (quarticChamberBDEFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG38 hc =>
          exact QuarticChamberResidual810.rBDEFG38 hc
        | cBDEFG39 hc =>
          exact QuarticChamberResidual810.rBDEFG39 hc
        | cBDEFG40 hc =>
          exact (quarticChamberBDEFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG41 hc =>
          exact (quarticChamberBDEFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG42 hc =>
          exact QuarticChamberResidual810.rBDEFG42 hc
        | cBDEFG43 hc =>
          exact QuarticChamberResidual810.rBDEFG43 hc
        | cBDEFG44 hc =>
          exact QuarticChamberResidual810.rBDEFG44 hc
        | cBDEFG45 hc =>
          exact QuarticChamberResidual810.rBDEFG45 hc
        | cBDEFG46 hc =>
          exact (quarticChamberBDEFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG47 hc =>
          exact (quarticChamberBDEFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG48 hc =>
          exact QuarticChamberResidual810.rBDEFG48 hc
        | cBDEFG49 hc =>
          exact (quarticChamberBDEFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG50 hc =>
          exact (quarticChamberBDEFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG51 hc =>
          exact (quarticChamberBDEFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG52 hc =>
          exact (quarticChamberBDEFG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG53 hc =>
          exact (quarticChamberBDEFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG54 hc =>
          exact (quarticChamberBDEFG54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG0 hc =>
          exact (quarticChamberCDEFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG1 hc =>
          exact QuarticChamberResidual810.rCDEFG1 hc
        | cCDEFG2 hc =>
          exact (quarticChamberCDEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG3 hc =>
          exact QuarticChamberResidual810.rCDEFG3 hc
        | cCDEFG4 hc =>
          exact QuarticChamberResidual810.rCDEFG4 hc
        | cCDEFG5 hc =>
          exact QuarticChamberResidual810.rCDEFG5 hc
        | cCDEFG6 hc =>
          exact QuarticChamberResidual810.rCDEFG6 hc
        | cCDEFG7 hc =>
          exact QuarticChamberResidual810.rCDEFG7 hc
        | cCDEFG8 hc =>
          exact QuarticChamberResidual810.rCDEFG8 hc
        | cCDEFG9 hc =>
          exact QuarticChamberResidual810.rCDEFG9 hc
        | cCDEFG10 hc =>
          exact QuarticChamberResidual810.rCDEFG10 hc
        | cCDEFG11 hc =>
          exact QuarticChamberResidual810.rCDEFG11 hc
        | cCDEFG12 hc =>
          exact QuarticChamberResidual810.rCDEFG12 hc
        | cCDEFG13 hc =>
          exact QuarticChamberResidual810.rCDEFG13 hc
        | cCDEFG14 hc =>
          exact QuarticChamberResidual810.rCDEFG14 hc
        | cCDEFG15 hc =>
          exact (quarticChamberCDEFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG16 hc =>
          exact QuarticChamberResidual810.rCDEFG16 hc
        | cCDEFG17 hc =>
          exact (quarticChamberCDEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG18 hc =>
          exact (quarticChamberCDEFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG19 hc =>
          exact QuarticChamberResidual810.rCDEFG19 hc
        | cCDEFG20 hc =>
          exact QuarticChamberResidual810.rCDEFG20 hc
        | cCDEFG21 hc =>
          exact (quarticChamberCDEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG22 hc =>
          exact QuarticChamberResidual810.rCDEFG22 hc
        | cCDEFG23 hc =>
          exact (quarticChamberCDEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG24 hc =>
          exact (quarticChamberCDEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG25 hc =>
          exact QuarticChamberResidual810.rCDEFG25 hc
        | cCDEFG26 hc =>
          exact QuarticChamberResidual810.rCDEFG26 hc
        | cCDEFG27 hc =>
          exact (quarticChamberCDEFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG28 hc =>
          exact QuarticChamberResidual810.rCDEFG28 hc
        | cCDEFG29 hc =>
          exact (quarticChamberCDEFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG30 hc =>
          exact QuarticChamberResidual810.rCDEFG30 hc
        | cCDEFG31 hc =>
          exact QuarticChamberResidual810.rCDEFG31 hc
        | cCDEFG32 hc =>
          exact (quarticChamberCDEFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG33 hc =>
          exact (quarticChamberCDEFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG34 hc =>
          exact QuarticChamberResidual810.rCDEFG34 hc
        | cCDEFG35 hc =>
          exact (quarticChamberCDEFG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG36 hc =>
          exact QuarticChamberResidual810.rCDEFG36 hc
        | cCDEFG37 hc =>
          exact (quarticChamberCDEFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG38 hc =>
          exact QuarticChamberResidual810.rCDEFG38 hc
        | cCDEFG39 hc =>
          exact QuarticChamberResidual810.rCDEFG39 hc
        | cCDEFG40 hc =>
          exact (quarticChamberCDEFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG41 hc =>
          exact (quarticChamberCDEFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG42 hc =>
          exact QuarticChamberResidual810.rCDEFG42 hc
        | cCDEFG43 hc =>
          exact QuarticChamberResidual810.rCDEFG43 hc
        | cCDEFG44 hc =>
          exact QuarticChamberResidual810.rCDEFG44 hc
        | cCDEFG45 hc =>
          exact QuarticChamberResidual810.rCDEFG45 hc
        | cCDEFG46 hc =>
          exact (quarticChamberCDEFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG47 hc =>
          exact (quarticChamberCDEFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG48 hc =>
          exact (quarticChamberCDEFG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG49 hc =>
          exact (quarticChamberCDEFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG50 hc =>
          exact (quarticChamberCDEFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG51 hc =>
          exact (quarticChamberCDEFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG52 hc =>
          exact (quarticChamberCDEFG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG53 hc =>
          exact (quarticChamberCDEFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG54 hc =>
          exact (quarticChamberCDEFG54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
      | size6 h =>
        cases h with
        | cBCDEFG0 hc =>
          exact QuarticChamberResidual810.rBCDEFG0 hc
        | cBCDEFG1 hc =>
          exact QuarticChamberResidual810.rBCDEFG1 hc
        | cBCDEFG2 hc =>
          exact (quarticChamberBCDEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG3 hc =>
          exact QuarticChamberResidual810.rBCDEFG3 hc
        | cBCDEFG4 hc =>
          exact (quarticChamberBCDEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG5 hc =>
          exact QuarticChamberResidual810.rBCDEFG5 hc
        | cBCDEFG6 hc =>
          exact QuarticChamberResidual810.rBCDEFG6 hc
        | cBCDEFG7 hc =>
          exact QuarticChamberResidual810.rBCDEFG7 hc
        | cBCDEFG8 hc =>
          exact (quarticChamberBCDEFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG9 hc =>
          exact QuarticChamberResidual810.rBCDEFG9 hc
        | cBCDEFG10 hc =>
          exact QuarticChamberResidual810.rBCDEFG10 hc
        | cBCDEFG11 hc =>
          exact QuarticChamberResidual810.rBCDEFG11 hc
        | cBCDEFG12 hc =>
          exact QuarticChamberResidual810.rBCDEFG12 hc
        | cBCDEFG13 hc =>
          exact QuarticChamberResidual810.rBCDEFG13 hc
        | cBCDEFG14 hc =>
          exact (quarticChamberBCDEFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG15 hc =>
          exact QuarticChamberResidual810.rBCDEFG15 hc
        | cBCDEFG16 hc =>
          exact QuarticChamberResidual810.rBCDEFG16 hc
        | cBCDEFG17 hc =>
          exact (quarticChamberBCDEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG18 hc =>
          exact QuarticChamberResidual810.rBCDEFG18 hc
        | cBCDEFG19 hc =>
          exact QuarticChamberResidual810.rBCDEFG19 hc
        | cBCDEFG20 hc =>
          exact QuarticChamberResidual810.rBCDEFG20 hc
        | cBCDEFG21 hc =>
          exact QuarticChamberResidual810.rBCDEFG21 hc
        | cBCDEFG22 hc =>
          exact QuarticChamberResidual810.rBCDEFG22 hc
        | cBCDEFG23 hc =>
          exact QuarticChamberResidual810.rBCDEFG23 hc
        | cBCDEFG24 hc =>
          exact QuarticChamberResidual810.rBCDEFG24 hc
        | cBCDEFG25 hc =>
          exact QuarticChamberResidual810.rBCDEFG25 hc
        | cBCDEFG26 hc =>
          exact QuarticChamberResidual810.rBCDEFG26 hc
        | cBCDEFG27 hc =>
          exact (quarticChamberBCDEFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG28 hc =>
          exact (quarticChamberBCDEFG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG29 hc =>
          exact QuarticChamberResidual810.rBCDEFG29 hc
        | cBCDEFG30 hc =>
          exact QuarticChamberResidual810.rBCDEFG30 hc
        | cBCDEFG31 hc =>
          exact QuarticChamberResidual810.rBCDEFG31 hc
        | cBCDEFG32 hc =>
          exact (quarticChamberBCDEFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG33 hc =>
          exact (quarticChamberBCDEFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG34 hc =>
          exact QuarticChamberResidual810.rBCDEFG34 hc
        | cBCDEFG35 hc =>
          exact (quarticChamberBCDEFG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG36 hc =>
          exact QuarticChamberResidual810.rBCDEFG36 hc
        | cBCDEFG37 hc =>
          exact QuarticChamberResidual810.rBCDEFG37 hc
        | cBCDEFG38 hc =>
          exact (quarticChamberBCDEFG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG39 hc =>
          exact (quarticChamberBCDEFG39810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG40 hc =>
          exact (quarticChamberBCDEFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG41 hc =>
          exact QuarticChamberResidual810.rBCDEFG41 hc
        | cBCDEFG42 hc =>
          exact (quarticChamberBCDEFG42810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG43 hc =>
          exact QuarticChamberResidual810.rBCDEFG43 hc
        | cBCDEFG44 hc =>
          exact QuarticChamberResidual810.rBCDEFG44 hc
        | cBCDEFG45 hc =>
          exact (quarticChamberBCDEFG45810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG46 hc =>
          exact (quarticChamberBCDEFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG47 hc =>
          exact QuarticChamberResidual810.rBCDEFG47 hc
        | cBCDEFG48 hc =>
          exact (quarticChamberBCDEFG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG49 hc =>
          exact (quarticChamberBCDEFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG50 hc =>
          exact QuarticChamberResidual810.rBCDEFG50 hc
        | cBCDEFG51 hc =>
          exact QuarticChamberResidual810.rBCDEFG51 hc
        | cBCDEFG52 hc =>
          exact (quarticChamberBCDEFG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG53 hc =>
          exact QuarticChamberResidual810.rBCDEFG53 hc
        | cBCDEFG54 hc =>
          exact QuarticChamberResidual810.rBCDEFG54 hc
        | cBCDEFG55 hc =>
          exact QuarticChamberResidual810.rBCDEFG55 hc
        | cBCDEFG56 hc =>
          exact (quarticChamberBCDEFG56810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG57 hc =>
          exact (quarticChamberBCDEFG57810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG58 hc =>
          exact QuarticChamberResidual810.rBCDEFG58 hc
        | cBCDEFG59 hc =>
          exact (quarticChamberBCDEFG59810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG60 hc =>
          exact QuarticChamberResidual810.rBCDEFG60 hc
        | cBCDEFG61 hc =>
          exact QuarticChamberResidual810.rBCDEFG61 hc
        | cBCDEFG62 hc =>
          exact (quarticChamberBCDEFG62810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG63 hc =>
          exact (quarticChamberBCDEFG63810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG64 hc =>
          exact (quarticChamberBCDEFG64810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG65 hc =>
          exact QuarticChamberResidual810.rBCDEFG65 hc
        | cBCDEFG66 hc =>
          exact (quarticChamberBCDEFG66810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG67 hc =>
          exact (quarticChamberBCDEFG67810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG68 hc =>
          exact QuarticChamberResidual810.rBCDEFG68 hc
        | cBCDEFG69 hc =>
          exact (quarticChamberBCDEFG69810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG70 hc =>
          exact (quarticChamberBCDEFG70810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG71 hc =>
          exact QuarticChamberResidual810.rBCDEFG71 hc
        | cBCDEFG72 hc =>
          exact (quarticChamberBCDEFG72810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG73 hc =>
          exact (quarticChamberBCDEFG73810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG74 hc =>
          exact (quarticChamberBCDEFG74810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG75 hc =>
          exact QuarticChamberResidual810.rBCDEFG75 hc
        | cBCDEFG76 hc =>
          exact (quarticChamberBCDEFG76810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG77 hc =>
          exact (quarticChamberBCDEFG77810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG78 hc =>
          exact QuarticChamberResidual810.rBCDEFG78 hc
        | cBCDEFG79 hc =>
          exact QuarticChamberResidual810.rBCDEFG79 hc
        | cBCDEFG80 hc =>
          exact QuarticChamberResidual810.rBCDEFG80 hc
        | cBCDEFG81 hc =>
          exact QuarticChamberResidual810.rBCDEFG81 hc
        | cBCDEFG82 hc =>
          exact QuarticChamberResidual810.rBCDEFG82 hc
        | cBCDEFG83 hc =>
          exact QuarticChamberResidual810.rBCDEFG83 hc
        | cBCDEFG84 hc =>
          exact QuarticChamberResidual810.rBCDEFG84 hc
        | cBCDEFG85 hc =>
          exact QuarticChamberResidual810.rBCDEFG85 hc
        | cBCDEFG86 hc =>
          exact QuarticChamberResidual810.rBCDEFG86 hc
        | cBCDEFG87 hc =>
          exact QuarticChamberResidual810.rBCDEFG87 hc
        | cBCDEFG88 hc =>
          exact (quarticChamberBCDEFG88810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG89 hc =>
          exact (quarticChamberBCDEFG89810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG90 hc =>
          exact QuarticChamberResidual810.rBCDEFG90 hc
        | cBCDEFG91 hc =>
          exact (quarticChamberBCDEFG91810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG92 hc =>
          exact (quarticChamberBCDEFG92810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG93 hc =>
          exact QuarticChamberResidual810.rBCDEFG93 hc
        | cBCDEFG94 hc =>
          exact QuarticChamberResidual810.rBCDEFG94 hc
        | cBCDEFG95 hc =>
          exact (quarticChamberBCDEFG95810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG96 hc =>
          exact QuarticChamberResidual810.rBCDEFG96 hc
        | cBCDEFG97 hc =>
          exact (quarticChamberBCDEFG97810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG98 hc =>
          exact (quarticChamberBCDEFG98810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG99 hc =>
          exact (quarticChamberBCDEFG99810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG100 hc =>
          exact QuarticChamberResidual810.rBCDEFG100 hc
        | cBCDEFG101 hc =>
          exact (quarticChamberBCDEFG101810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG102 hc =>
          exact QuarticChamberResidual810.rBCDEFG102 hc
        | cBCDEFG103 hc =>
          exact (quarticChamberBCDEFG103810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG104 hc =>
          exact QuarticChamberResidual810.rBCDEFG104 hc
        | cBCDEFG105 hc =>
          exact QuarticChamberResidual810.rBCDEFG105 hc
        | cBCDEFG106 hc =>
          exact (quarticChamberBCDEFG106810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG107 hc =>
          exact (quarticChamberBCDEFG107810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG108 hc =>
          exact QuarticChamberResidual810.rBCDEFG108 hc
        | cBCDEFG109 hc =>
          exact (quarticChamberBCDEFG109810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG110 hc =>
          exact (quarticChamberBCDEFG110810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG111 hc =>
          exact (quarticChamberBCDEFG111810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG112 hc =>
          exact QuarticChamberResidual810.rBCDEFG112 hc
        | cBCDEFG113 hc =>
          exact QuarticChamberResidual810.rBCDEFG113 hc
        | cBCDEFG114 hc =>
          exact QuarticChamberResidual810.rBCDEFG114 hc
        | cBCDEFG115 hc =>
          exact QuarticChamberResidual810.rBCDEFG115 hc
        | cBCDEFG116 hc =>
          exact (quarticChamberBCDEFG116810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG117 hc =>
          exact (quarticChamberBCDEFG117810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG118 hc =>
          exact QuarticChamberResidual810.rBCDEFG118 hc
        | cBCDEFG119 hc =>
          exact QuarticChamberResidual810.rBCDEFG119 hc
        | cBCDEFG120 hc =>
          exact QuarticChamberResidual810.rBCDEFG120 hc
        | cBCDEFG121 hc =>
          exact QuarticChamberResidual810.rBCDEFG121 hc
        | cBCDEFG122 hc =>
          exact QuarticChamberResidual810.rBCDEFG122 hc
        | cBCDEFG123 hc =>
          exact QuarticChamberResidual810.rBCDEFG123 hc
        | cBCDEFG124 hc =>
          exact (quarticChamberBCDEFG124810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG125 hc =>
          exact (quarticChamberBCDEFG125810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG126 hc =>
          exact QuarticChamberResidual810.rBCDEFG126 hc
        | cBCDEFG127 hc =>
          exact QuarticChamberResidual810.rBCDEFG127 hc
        | cBCDEFG128 hc =>
          exact (quarticChamberBCDEFG128810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG129 hc =>
          exact (quarticChamberBCDEFG129810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG130 hc =>
          exact (quarticChamberBCDEFG130810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG131 hc =>
          exact (quarticChamberBCDEFG131810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG132 hc =>
          exact (quarticChamberBCDEFG132810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG133 hc =>
          exact (quarticChamberBCDEFG133810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG134 hc =>
          exact (quarticChamberBCDEFG134810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
  · exact Or.inr hABCDEFG

#print axioms normalized810ScaleZero_quarticChamberResidual

end QuarticChamberResidual810

end Max11DegreeRoutes
