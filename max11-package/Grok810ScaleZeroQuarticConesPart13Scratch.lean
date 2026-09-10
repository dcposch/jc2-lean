import Grok810ScaleZeroQuarticConesPart12Scratch

/-! # Part 13 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_DAG {nD nA nG : ℕ}
    (hxy : 2 * nD = 5 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_lt_trans_DBA {nD nB nA : ℕ}
    (hxy : 3 * nD < 5 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_eq_lt_DBA {nD nB nA : ℕ}
    (hxy : 3 * nD = 5 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_lt_trans_DBC {nD nB nC : ℕ}
    (hxy : 3 * nD < 5 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_eq_lt_DBC {nD nB nC : ℕ}
    (hxy : 3 * nD = 5 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_lt_trans_DBE {nD nB nE : ℕ}
    (hxy : 3 * nD < 5 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_eq_lt_DBE {nD nB nE : ℕ}
    (hxy : 3 * nD = 5 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_lt_trans_DBF {nD nB nF : ℕ}
    (hxy : 3 * nD < 5 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_eq_lt_DBF {nD nB nF : ℕ}
    (hxy : 3 * nD = 5 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_lt_trans_DBG {nD nB nG : ℕ}
    (hxy : 3 * nD < 5 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_eq_lt_DBG {nD nB nG : ℕ}
    (hxy : 3 * nD = 5 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_lt_trans_DCA {nD nC nA : ℕ}
    (hxy : 4 * nD < 5 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_eq_lt_DCA {nD nC nA : ℕ}
    (hxy : 4 * nD = 5 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_lt_trans_DCB {nD nC nB : ℕ}
    (hxy : 4 * nD < 5 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_eq_lt_DCB {nD nC nB : ℕ}
    (hxy : 4 * nD = 5 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_lt_trans_DCE {nD nC nE : ℕ}
    (hxy : 4 * nD < 5 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_eq_lt_DCE {nD nC nE : ℕ}
    (hxy : 4 * nD = 5 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_lt_trans_DCF {nD nC nF : ℕ}
    (hxy : 4 * nD < 5 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_eq_lt_DCF {nD nC nF : ℕ}
    (hxy : 4 * nD = 5 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_lt_trans_DCG {nD nC nG : ℕ}
    (hxy : 4 * nD < 5 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_eq_lt_DCG {nD nC nG : ℕ}
    (hxy : 4 * nD = 5 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_lt_trans_DEA {nD nE nA : ℕ}
    (hxy : 6 * nD < 5 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_eq_lt_DEA {nD nE nA : ℕ}
    (hxy : 6 * nD = 5 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_lt_trans_DEB {nD nE nB : ℕ}
    (hxy : 6 * nD < 5 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nD < 5 * nB := by omega

end QuarticExhaust810

end Max11DegreeRoutes
