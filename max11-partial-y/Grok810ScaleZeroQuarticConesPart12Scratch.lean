import Grok810ScaleZeroQuarticConesPart11Scratch

/-! # Part 12 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_CFD {nC nF nD : ℕ}
    (hxy : 7 * nC = 4 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_lt_trans_CFE {nC nF nE : ℕ}
    (hxy : 7 * nC < 4 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_eq_lt_CFE {nC nF nE : ℕ}
    (hxy : 7 * nC = 4 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_lt_trans_CFG {nC nF nG : ℕ}
    (hxy : 7 * nC < 4 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_eq_lt_CFG {nC nF nG : ℕ}
    (hxy : 7 * nC = 4 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_lt_trans_CGA {nC nG nA : ℕ}
    (hxy : 8 * nC < 4 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_eq_lt_CGA {nC nG nA : ℕ}
    (hxy : 8 * nC = 4 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_lt_trans_CGB {nC nG nB : ℕ}
    (hxy : 8 * nC < 4 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_eq_lt_CGB {nC nG nB : ℕ}
    (hxy : 8 * nC = 4 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_lt_trans_CGD {nC nG nD : ℕ}
    (hxy : 8 * nC < 4 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_eq_lt_CGD {nC nG nD : ℕ}
    (hxy : 8 * nC = 4 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_lt_trans_CGE {nC nG nE : ℕ}
    (hxy : 8 * nC < 4 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_eq_lt_CGE {nC nG nE : ℕ}
    (hxy : 8 * nC = 4 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_lt_trans_CGF {nC nG nF : ℕ}
    (hxy : 8 * nC < 4 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_eq_lt_CGF {nC nG nF : ℕ}
    (hxy : 8 * nC = 4 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_lt_trans_DAB {nD nA nB : ℕ}
    (hxy : 2 * nD < 5 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_eq_lt_DAB {nD nA nB : ℕ}
    (hxy : 2 * nD = 5 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_lt_trans_DAC {nD nA nC : ℕ}
    (hxy : 2 * nD < 5 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_eq_lt_DAC {nD nA nC : ℕ}
    (hxy : 2 * nD = 5 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_lt_trans_DAE {nD nA nE : ℕ}
    (hxy : 2 * nD < 5 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_eq_lt_DAE {nD nA nE : ℕ}
    (hxy : 2 * nD = 5 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_lt_trans_DAF {nD nA nF : ℕ}
    (hxy : 2 * nD < 5 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_eq_lt_DAF {nD nA nF : ℕ}
    (hxy : 2 * nD = 5 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_lt_trans_DAG {nD nA nG : ℕ}
    (hxy : 2 * nD < 5 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nD < 5 * nG := by omega

end QuarticExhaust810

end Max11DegreeRoutes
