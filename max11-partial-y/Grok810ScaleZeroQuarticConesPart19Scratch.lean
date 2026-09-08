import Grok810ScaleZeroQuarticConesPart18Scratch

/-! # Part 19 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_FDB {nF nD nB : ℕ}
    (hxy : 5 * nF = 7 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_lt_trans_FDC {nF nD nC : ℕ}
    (hxy : 5 * nF < 7 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_eq_lt_FDC {nF nD nC : ℕ}
    (hxy : 5 * nF = 7 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_lt_trans_FDE {nF nD nE : ℕ}
    (hxy : 5 * nF < 7 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_eq_lt_FDE {nF nD nE : ℕ}
    (hxy : 5 * nF = 7 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_lt_trans_FDG {nF nD nG : ℕ}
    (hxy : 5 * nF < 7 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_eq_lt_FDG {nF nD nG : ℕ}
    (hxy : 5 * nF = 7 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_lt_trans_FEA {nF nE nA : ℕ}
    (hxy : 6 * nF < 7 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_eq_lt_FEA {nF nE nA : ℕ}
    (hxy : 6 * nF = 7 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_lt_trans_FEB {nF nE nB : ℕ}
    (hxy : 6 * nF < 7 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_eq_lt_FEB {nF nE nB : ℕ}
    (hxy : 6 * nF = 7 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_lt_trans_FEC {nF nE nC : ℕ}
    (hxy : 6 * nF < 7 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_eq_lt_FEC {nF nE nC : ℕ}
    (hxy : 6 * nF = 7 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_lt_trans_FED {nF nE nD : ℕ}
    (hxy : 6 * nF < 7 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_eq_lt_FED {nF nE nD : ℕ}
    (hxy : 6 * nF = 7 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_lt_trans_FEG {nF nE nG : ℕ}
    (hxy : 6 * nF < 7 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_eq_lt_FEG {nF nE nG : ℕ}
    (hxy : 6 * nF = 7 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_lt_trans_FGA {nF nG nA : ℕ}
    (hxy : 8 * nF < 7 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_eq_lt_FGA {nF nG nA : ℕ}
    (hxy : 8 * nF = 7 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_lt_trans_FGB {nF nG nB : ℕ}
    (hxy : 8 * nF < 7 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_eq_lt_FGB {nF nG nB : ℕ}
    (hxy : 8 * nF = 7 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_lt_trans_FGC {nF nG nC : ℕ}
    (hxy : 8 * nF < 7 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_eq_lt_FGC {nF nG nC : ℕ}
    (hxy : 8 * nF = 7 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_lt_trans_FGD {nF nG nD : ℕ}
    (hxy : 8 * nF < 7 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nF < 7 * nD := by omega

end QuarticExhaust810

end Max11DegreeRoutes
