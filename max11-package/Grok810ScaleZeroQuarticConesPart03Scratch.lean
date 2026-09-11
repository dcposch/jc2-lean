import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 3 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticEq_GA_to_raw {nG nA : ℕ}
    (h : nG = 4 * nA) : 2 * nG = 8 * nA := by omega

theorem quarticCmp_GC_of_raw {nG nC : ℕ}
    (h : 4 * nG < 8 * nC) : nG < 2 * nC := by omega

theorem quarticCmp_GC_to_raw {nG nC : ℕ}
    (h : nG < 2 * nC) : 4 * nG < 8 * nC := by omega

theorem quarticEq_GC_of_raw {nG nC : ℕ}
    (h : 4 * nG = 8 * nC) : nG = 2 * nC := by omega

theorem quarticEq_GC_to_raw {nG nC : ℕ}
    (h : nG = 2 * nC) : 4 * nG = 8 * nC := by omega

theorem quarticCmp_GE_of_raw {nG nE : ℕ}
    (h : 6 * nG < 8 * nE) : 3 * nG < 4 * nE := by omega

theorem quarticCmp_GE_to_raw {nG nE : ℕ}
    (h : 3 * nG < 4 * nE) : 6 * nG < 8 * nE := by omega

theorem quarticEq_GE_of_raw {nG nE : ℕ}
    (h : 6 * nG = 8 * nE) : 3 * nG = 4 * nE := by omega

theorem quarticEq_GE_to_raw {nG nE : ℕ}
    (h : 3 * nG = 4 * nE) : 6 * nG = 8 * nE := by omega

theorem quarticCmp_AB_of_zero {nA nB : ℕ}
    (hx0 : nA = 0) (hy : 0 < nB) :
    3 * nA < 2 * nB := by omega

theorem quarticCmp_AC_of_zero {nA nC : ℕ}
    (hx0 : nA = 0) (hy : 0 < nC) :
    2 * nA < nC := by omega

theorem quarticCmp_AD_of_zero {nA nD : ℕ}
    (hx0 : nA = 0) (hy : 0 < nD) :
    5 * nA < 2 * nD := by omega

theorem quarticCmp_AE_of_zero {nA nE : ℕ}
    (hx0 : nA = 0) (hy : 0 < nE) :
    3 * nA < nE := by omega

theorem quarticCmp_AF_of_zero {nA nF : ℕ}
    (hx0 : nA = 0) (hy : 0 < nF) :
    7 * nA < 2 * nF := by omega

theorem quarticCmp_AG_of_zero {nA nG : ℕ}
    (hx0 : nA = 0) (hy : 0 < nG) :
    4 * nA < nG := by omega

theorem quarticCmp_BA_of_zero {nB nA : ℕ}
    (hx0 : nB = 0) (hy : 0 < nA) :
    2 * nB < 3 * nA := by omega

theorem quarticCmp_BC_of_zero {nB nC : ℕ}
    (hx0 : nB = 0) (hy : 0 < nC) :
    4 * nB < 3 * nC := by omega

theorem quarticCmp_BD_of_zero {nB nD : ℕ}
    (hx0 : nB = 0) (hy : 0 < nD) :
    5 * nB < 3 * nD := by omega

theorem quarticCmp_BE_of_zero {nB nE : ℕ}
    (hx0 : nB = 0) (hy : 0 < nE) :
    2 * nB < nE := by omega

theorem quarticCmp_BF_of_zero {nB nF : ℕ}
    (hx0 : nB = 0) (hy : 0 < nF) :
    7 * nB < 3 * nF := by omega

theorem quarticCmp_BG_of_zero {nB nG : ℕ}
    (hx0 : nB = 0) (hy : 0 < nG) :
    8 * nB < 3 * nG := by omega

theorem quarticCmp_CA_of_zero {nC nA : ℕ}
    (hx0 : nC = 0) (hy : 0 < nA) :
    nC < 2 * nA := by omega

theorem quarticCmp_CB_of_zero {nC nB : ℕ}
    (hx0 : nC = 0) (hy : 0 < nB) :
    3 * nC < 4 * nB := by omega

theorem quarticCmp_CD_of_zero {nC nD : ℕ}
    (hx0 : nC = 0) (hy : 0 < nD) :
    5 * nC < 4 * nD := by omega

end QuarticExhaust810

end Max11DegreeRoutes
