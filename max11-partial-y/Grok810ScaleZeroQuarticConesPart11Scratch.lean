import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 11 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_CDA {nC nD nA : ℕ}
    (hxy : 5 * nC = 4 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_lt_trans_CDB {nC nD nB : ℕ}
    (hxy : 5 * nC < 4 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_eq_lt_CDB {nC nD nB : ℕ}
    (hxy : 5 * nC = 4 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_lt_trans_CDE {nC nD nE : ℕ}
    (hxy : 5 * nC < 4 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_eq_lt_CDE {nC nD nE : ℕ}
    (hxy : 5 * nC = 4 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_lt_trans_CDF {nC nD nF : ℕ}
    (hxy : 5 * nC < 4 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_eq_lt_CDF {nC nD nF : ℕ}
    (hxy : 5 * nC = 4 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_lt_trans_CDG {nC nD nG : ℕ}
    (hxy : 5 * nC < 4 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_eq_lt_CDG {nC nD nG : ℕ}
    (hxy : 5 * nC = 4 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_lt_trans_CEA {nC nE nA : ℕ}
    (hxy : 6 * nC < 4 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_eq_lt_CEA {nC nE nA : ℕ}
    (hxy : 6 * nC = 4 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_lt_trans_CEB {nC nE nB : ℕ}
    (hxy : 6 * nC < 4 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_eq_lt_CEB {nC nE nB : ℕ}
    (hxy : 6 * nC = 4 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_lt_trans_CED {nC nE nD : ℕ}
    (hxy : 6 * nC < 4 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_eq_lt_CED {nC nE nD : ℕ}
    (hxy : 6 * nC = 4 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_lt_trans_CEF {nC nE nF : ℕ}
    (hxy : 6 * nC < 4 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_eq_lt_CEF {nC nE nF : ℕ}
    (hxy : 6 * nC = 4 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_lt_trans_CEG {nC nE nG : ℕ}
    (hxy : 6 * nC < 4 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_eq_lt_CEG {nC nE nG : ℕ}
    (hxy : 6 * nC = 4 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_lt_trans_CFA {nC nF nA : ℕ}
    (hxy : 7 * nC < 4 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_eq_lt_CFA {nC nF nA : ℕ}
    (hxy : 7 * nC = 4 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_lt_trans_CFB {nC nF nB : ℕ}
    (hxy : 7 * nC < 4 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_eq_lt_CFB {nC nF nB : ℕ}
    (hxy : 7 * nC = 4 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_lt_trans_CFD {nC nF nD : ℕ}
    (hxy : 7 * nC < 4 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nC < 4 * nD := by omega

end QuarticExhaust810

end Max11DegreeRoutes
