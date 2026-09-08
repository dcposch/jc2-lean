import Grok810ScaleZeroQuarticConesPart07Scratch

/-! # Part 8 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_BAG {nB nA nG : ℕ}
    (hxy : 2 * nB = 3 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_lt_trans_BCA {nB nC nA : ℕ}
    (hxy : 4 * nB < 3 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_eq_lt_BCA {nB nC nA : ℕ}
    (hxy : 4 * nB = 3 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_lt_trans_BCD {nB nC nD : ℕ}
    (hxy : 4 * nB < 3 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_eq_lt_BCD {nB nC nD : ℕ}
    (hxy : 4 * nB = 3 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_lt_trans_BCE {nB nC nE : ℕ}
    (hxy : 4 * nB < 3 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_eq_lt_BCE {nB nC nE : ℕ}
    (hxy : 4 * nB = 3 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_lt_trans_BCF {nB nC nF : ℕ}
    (hxy : 4 * nB < 3 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_eq_lt_BCF {nB nC nF : ℕ}
    (hxy : 4 * nB = 3 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_lt_trans_BCG {nB nC nG : ℕ}
    (hxy : 4 * nB < 3 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_eq_lt_BCG {nB nC nG : ℕ}
    (hxy : 4 * nB = 3 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_lt_trans_BDA {nB nD nA : ℕ}
    (hxy : 5 * nB < 3 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_eq_lt_BDA {nB nD nA : ℕ}
    (hxy : 5 * nB = 3 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_lt_trans_BDC {nB nD nC : ℕ}
    (hxy : 5 * nB < 3 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_eq_lt_BDC {nB nD nC : ℕ}
    (hxy : 5 * nB = 3 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_lt_trans_BDE {nB nD nE : ℕ}
    (hxy : 5 * nB < 3 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_eq_lt_BDE {nB nD nE : ℕ}
    (hxy : 5 * nB = 3 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_lt_trans_BDF {nB nD nF : ℕ}
    (hxy : 5 * nB < 3 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_eq_lt_BDF {nB nD nF : ℕ}
    (hxy : 5 * nB = 3 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_lt_trans_BDG {nB nD nG : ℕ}
    (hxy : 5 * nB < 3 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_eq_lt_BDG {nB nD nG : ℕ}
    (hxy : 5 * nB = 3 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_lt_trans_BEA {nB nE nA : ℕ}
    (hxy : 6 * nB < 3 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_eq_lt_BEA {nB nE nA : ℕ}
    (hxy : 6 * nB = 3 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_lt_trans_BEC {nB nE nC : ℕ}
    (hxy : 6 * nB < 3 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nB < 3 * nC := by omega

end QuarticExhaust810

end Max11DegreeRoutes
