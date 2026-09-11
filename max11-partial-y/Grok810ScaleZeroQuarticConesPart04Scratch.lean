import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 4 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticCmp_CE_of_zero {nC nE : ℕ}
    (hx0 : nC = 0) (hy : 0 < nE) :
    3 * nC < 2 * nE := by omega

theorem quarticCmp_CF_of_zero {nC nF : ℕ}
    (hx0 : nC = 0) (hy : 0 < nF) :
    7 * nC < 4 * nF := by omega

theorem quarticCmp_CG_of_zero {nC nG : ℕ}
    (hx0 : nC = 0) (hy : 0 < nG) :
    2 * nC < nG := by omega

theorem quarticCmp_DA_of_zero {nD nA : ℕ}
    (hx0 : nD = 0) (hy : 0 < nA) :
    2 * nD < 5 * nA := by omega

theorem quarticCmp_DB_of_zero {nD nB : ℕ}
    (hx0 : nD = 0) (hy : 0 < nB) :
    3 * nD < 5 * nB := by omega

theorem quarticCmp_DC_of_zero {nD nC : ℕ}
    (hx0 : nD = 0) (hy : 0 < nC) :
    4 * nD < 5 * nC := by omega

theorem quarticCmp_DE_of_zero {nD nE : ℕ}
    (hx0 : nD = 0) (hy : 0 < nE) :
    6 * nD < 5 * nE := by omega

theorem quarticCmp_DF_of_zero {nD nF : ℕ}
    (hx0 : nD = 0) (hy : 0 < nF) :
    7 * nD < 5 * nF := by omega

theorem quarticCmp_DG_of_zero {nD nG : ℕ}
    (hx0 : nD = 0) (hy : 0 < nG) :
    8 * nD < 5 * nG := by omega

theorem quarticCmp_EA_of_zero {nE nA : ℕ}
    (hx0 : nE = 0) (hy : 0 < nA) :
    nE < 3 * nA := by omega

theorem quarticCmp_EB_of_zero {nE nB : ℕ}
    (hx0 : nE = 0) (hy : 0 < nB) :
    nE < 2 * nB := by omega

theorem quarticCmp_EC_of_zero {nE nC : ℕ}
    (hx0 : nE = 0) (hy : 0 < nC) :
    2 * nE < 3 * nC := by omega

theorem quarticCmp_ED_of_zero {nE nD : ℕ}
    (hx0 : nE = 0) (hy : 0 < nD) :
    5 * nE < 6 * nD := by omega

theorem quarticCmp_EF_of_zero {nE nF : ℕ}
    (hx0 : nE = 0) (hy : 0 < nF) :
    7 * nE < 6 * nF := by omega

theorem quarticCmp_EG_of_zero {nE nG : ℕ}
    (hx0 : nE = 0) (hy : 0 < nG) :
    4 * nE < 3 * nG := by omega

theorem quarticCmp_FA_of_zero {nF nA : ℕ}
    (hx0 : nF = 0) (hy : 0 < nA) :
    2 * nF < 7 * nA := by omega

theorem quarticCmp_FB_of_zero {nF nB : ℕ}
    (hx0 : nF = 0) (hy : 0 < nB) :
    3 * nF < 7 * nB := by omega

theorem quarticCmp_FC_of_zero {nF nC : ℕ}
    (hx0 : nF = 0) (hy : 0 < nC) :
    4 * nF < 7 * nC := by omega

theorem quarticCmp_FD_of_zero {nF nD : ℕ}
    (hx0 : nF = 0) (hy : 0 < nD) :
    5 * nF < 7 * nD := by omega

theorem quarticCmp_FE_of_zero {nF nE : ℕ}
    (hx0 : nF = 0) (hy : 0 < nE) :
    6 * nF < 7 * nE := by omega

theorem quarticCmp_FG_of_zero {nF nG : ℕ}
    (hx0 : nF = 0) (hy : 0 < nG) :
    8 * nF < 7 * nG := by omega

theorem quarticCmp_GA_of_zero {nG nA : ℕ}
    (hx0 : nG = 0) (hy : 0 < nA) :
    nG < 4 * nA := by omega

theorem quarticCmp_GB_of_zero {nG nB : ℕ}
    (hx0 : nG = 0) (hy : 0 < nB) :
    3 * nG < 8 * nB := by omega

theorem quarticCmp_GC_of_zero {nG nC : ℕ}
    (hx0 : nG = 0) (hy : 0 < nC) :
    nG < 2 * nC := by omega

end QuarticExhaust810

end Max11DegreeRoutes
