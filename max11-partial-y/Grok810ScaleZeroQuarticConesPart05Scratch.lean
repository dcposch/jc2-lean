import Grok810ScaleZeroQuarticConesPart04Scratch

/-! # Part 5 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticCmp_GD_of_zero {nG nD : ℕ}
    (hx0 : nG = 0) (hy : 0 < nD) :
    5 * nG < 8 * nD := by omega

theorem quarticCmp_GE_of_zero {nG nE : ℕ}
    (hx0 : nG = 0) (hy : 0 < nE) :
    3 * nG < 4 * nE := by omega

theorem quarticCmp_GF_of_zero {nG nF : ℕ}
    (hx0 : nG = 0) (hy : 0 < nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_lt_trans_ABC {nA nB nC : ℕ}
    (hxy : 3 * nA < 2 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_eq_lt_ABC {nA nB nC : ℕ}
    (hxy : 3 * nA = 2 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_lt_trans_ABD {nA nB nD : ℕ}
    (hxy : 3 * nA < 2 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_eq_lt_ABD {nA nB nD : ℕ}
    (hxy : 3 * nA = 2 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_lt_trans_ABE {nA nB nE : ℕ}
    (hxy : 3 * nA < 2 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_eq_lt_ABE {nA nB nE : ℕ}
    (hxy : 3 * nA = 2 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_lt_trans_ABF {nA nB nF : ℕ}
    (hxy : 3 * nA < 2 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_eq_lt_ABF {nA nB nF : ℕ}
    (hxy : 3 * nA = 2 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_lt_trans_ABG {nA nB nG : ℕ}
    (hxy : 3 * nA < 2 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_eq_lt_ABG {nA nB nG : ℕ}
    (hxy : 3 * nA = 2 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_lt_trans_ACB {nA nC nB : ℕ}
    (hxy : 4 * nA < 2 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_eq_lt_ACB {nA nC nB : ℕ}
    (hxy : 4 * nA = 2 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_lt_trans_ACD {nA nC nD : ℕ}
    (hxy : 4 * nA < 2 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_eq_lt_ACD {nA nC nD : ℕ}
    (hxy : 4 * nA = 2 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_lt_trans_ACE {nA nC nE : ℕ}
    (hxy : 4 * nA < 2 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_eq_lt_ACE {nA nC nE : ℕ}
    (hxy : 4 * nA = 2 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_lt_trans_ACF {nA nC nF : ℕ}
    (hxy : 4 * nA < 2 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_eq_lt_ACF {nA nC nF : ℕ}
    (hxy : 4 * nA = 2 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_lt_trans_ACG {nA nC nG : ℕ}
    (hxy : 4 * nA < 2 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_eq_lt_ACG {nA nC nG : ℕ}
    (hxy : 4 * nA = 2 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_lt_trans_ADB {nA nD nB : ℕ}
    (hxy : 5 * nA < 2 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nA < 2 * nB := by omega

end QuarticExhaust810

end Max11DegreeRoutes
