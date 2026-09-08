import Grok810ScaleZeroQuarticConesPart09Scratch

/-! # Part 10 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_BGE {nB nG nE : ℕ}
    (hxy : 8 * nB = 3 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_lt_trans_BGF {nB nG nF : ℕ}
    (hxy : 8 * nB < 3 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_eq_lt_BGF {nB nG nF : ℕ}
    (hxy : 8 * nB = 3 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_lt_trans_CAB {nC nA nB : ℕ}
    (hxy : 2 * nC < 4 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_eq_lt_CAB {nC nA nB : ℕ}
    (hxy : 2 * nC = 4 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nC < 4 * nB := by omega

theorem quarticScore_lt_trans_CAD {nC nA nD : ℕ}
    (hxy : 2 * nC < 4 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_eq_lt_CAD {nC nA nD : ℕ}
    (hxy : 2 * nC = 4 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_lt_trans_CAE {nC nA nE : ℕ}
    (hxy : 2 * nC < 4 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_eq_lt_CAE {nC nA nE : ℕ}
    (hxy : 2 * nC = 4 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_lt_trans_CAF {nC nA nF : ℕ}
    (hxy : 2 * nC < 4 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_eq_lt_CAF {nC nA nF : ℕ}
    (hxy : 2 * nC = 4 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_lt_trans_CAG {nC nA nG : ℕ}
    (hxy : 2 * nC < 4 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_eq_lt_CAG {nC nA nG : ℕ}
    (hxy : 2 * nC = 4 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_lt_trans_CBA {nC nB nA : ℕ}
    (hxy : 3 * nC < 4 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_eq_lt_CBA {nC nB nA : ℕ}
    (hxy : 3 * nC = 4 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nC < 4 * nA := by omega

theorem quarticScore_lt_trans_CBD {nC nB nD : ℕ}
    (hxy : 3 * nC < 4 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_eq_lt_CBD {nC nB nD : ℕ}
    (hxy : 3 * nC = 4 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nC < 4 * nD := by omega

theorem quarticScore_lt_trans_CBE {nC nB nE : ℕ}
    (hxy : 3 * nC < 4 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_eq_lt_CBE {nC nB nE : ℕ}
    (hxy : 3 * nC = 4 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nC < 4 * nE := by omega

theorem quarticScore_lt_trans_CBF {nC nB nF : ℕ}
    (hxy : 3 * nC < 4 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_eq_lt_CBF {nC nB nF : ℕ}
    (hxy : 3 * nC = 4 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nC < 4 * nF := by omega

theorem quarticScore_lt_trans_CBG {nC nB nG : ℕ}
    (hxy : 3 * nC < 4 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_eq_lt_CBG {nC nB nG : ℕ}
    (hxy : 3 * nC = 4 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nC < 4 * nG := by omega

theorem quarticScore_lt_trans_CDA {nC nD nA : ℕ}
    (hxy : 5 * nC < 4 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nC < 4 * nA := by omega

end QuarticExhaust810

end Max11DegreeRoutes
