import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 2 of `Grok810ScaleZeroQuarticConesScratch`.

One declaration split out of `Grok810ScaleZeroQuarticConesScratch`; statements are byte-identical.
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
set_option maxHeartbeats 64000000

section QuarticExhaust810

variable {k : Type*} [Field k] [CharZero k]

theorem quarticEq_CE_to_raw {nC nE : ℕ}
    (h : 3 * nC = 2 * nE) : 6 * nC = 4 * nE := by omega

theorem quarticCmp_CG_of_raw {nC nG : ℕ}
    (h : 8 * nC < 4 * nG) : 2 * nC < nG := by omega

theorem quarticCmp_CG_to_raw {nC nG : ℕ}
    (h : 2 * nC < nG) : 8 * nC < 4 * nG := by omega

theorem quarticEq_CG_of_raw {nC nG : ℕ}
    (h : 8 * nC = 4 * nG) : 2 * nC = nG := by omega

theorem quarticEq_CG_to_raw {nC nG : ℕ}
    (h : 2 * nC = nG) : 8 * nC = 4 * nG := by omega

theorem quarticCmp_EA_of_raw {nE nA : ℕ}
    (h : 2 * nE < 6 * nA) : nE < 3 * nA := by omega

theorem quarticCmp_EA_to_raw {nE nA : ℕ}
    (h : nE < 3 * nA) : 2 * nE < 6 * nA := by omega

theorem quarticEq_EA_of_raw {nE nA : ℕ}
    (h : 2 * nE = 6 * nA) : nE = 3 * nA := by omega

theorem quarticEq_EA_to_raw {nE nA : ℕ}
    (h : nE = 3 * nA) : 2 * nE = 6 * nA := by omega

theorem quarticCmp_EB_of_raw {nE nB : ℕ}
    (h : 3 * nE < 6 * nB) : nE < 2 * nB := by omega

theorem quarticCmp_EB_to_raw {nE nB : ℕ}
    (h : nE < 2 * nB) : 3 * nE < 6 * nB := by omega

theorem quarticEq_EB_of_raw {nE nB : ℕ}
    (h : 3 * nE = 6 * nB) : nE = 2 * nB := by omega

theorem quarticEq_EB_to_raw {nE nB : ℕ}
    (h : nE = 2 * nB) : 3 * nE = 6 * nB := by omega

theorem quarticCmp_EC_of_raw {nE nC : ℕ}
    (h : 4 * nE < 6 * nC) : 2 * nE < 3 * nC := by omega

theorem quarticCmp_EC_to_raw {nE nC : ℕ}
    (h : 2 * nE < 3 * nC) : 4 * nE < 6 * nC := by omega

theorem quarticEq_EC_of_raw {nE nC : ℕ}
    (h : 4 * nE = 6 * nC) : 2 * nE = 3 * nC := by omega

theorem quarticEq_EC_to_raw {nE nC : ℕ}
    (h : 2 * nE = 3 * nC) : 4 * nE = 6 * nC := by omega

theorem quarticCmp_EG_of_raw {nE nG : ℕ}
    (h : 8 * nE < 6 * nG) : 4 * nE < 3 * nG := by omega

theorem quarticCmp_EG_to_raw {nE nG : ℕ}
    (h : 4 * nE < 3 * nG) : 8 * nE < 6 * nG := by omega

theorem quarticEq_EG_of_raw {nE nG : ℕ}
    (h : 8 * nE = 6 * nG) : 4 * nE = 3 * nG := by omega

theorem quarticEq_EG_to_raw {nE nG : ℕ}
    (h : 4 * nE = 3 * nG) : 8 * nE = 6 * nG := by omega

theorem quarticCmp_GA_of_raw {nG nA : ℕ}
    (h : 2 * nG < 8 * nA) : nG < 4 * nA := by omega

theorem quarticCmp_GA_to_raw {nG nA : ℕ}
    (h : nG < 4 * nA) : 2 * nG < 8 * nA := by omega

theorem quarticEq_GA_of_raw {nG nA : ℕ}
    (h : 2 * nG = 8 * nA) : nG = 4 * nA := by omega

end QuarticExhaust810

end Max11DegreeRoutes
