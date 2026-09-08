import Grok810ScaleZeroQuarticConesPart06Scratch

/-! # Part 7 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_AFD {nA nF nD : ℕ}
    (hxy : 7 * nA = 2 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_lt_trans_AFE {nA nF nE : ℕ}
    (hxy : 7 * nA < 2 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_eq_lt_AFE {nA nF nE : ℕ}
    (hxy : 7 * nA = 2 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_lt_trans_AFG {nA nF nG : ℕ}
    (hxy : 7 * nA < 2 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_eq_lt_AFG {nA nF nG : ℕ}
    (hxy : 7 * nA = 2 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_lt_trans_AGB {nA nG nB : ℕ}
    (hxy : 8 * nA < 2 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_eq_lt_AGB {nA nG nB : ℕ}
    (hxy : 8 * nA = 2 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_lt_trans_AGC {nA nG nC : ℕ}
    (hxy : 8 * nA < 2 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_eq_lt_AGC {nA nG nC : ℕ}
    (hxy : 8 * nA = 2 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_lt_trans_AGD {nA nG nD : ℕ}
    (hxy : 8 * nA < 2 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_eq_lt_AGD {nA nG nD : ℕ}
    (hxy : 8 * nA = 2 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_lt_trans_AGE {nA nG nE : ℕ}
    (hxy : 8 * nA < 2 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_eq_lt_AGE {nA nG nE : ℕ}
    (hxy : 8 * nA = 2 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_lt_trans_AGF {nA nG nF : ℕ}
    (hxy : 8 * nA < 2 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_eq_lt_AGF {nA nG nF : ℕ}
    (hxy : 8 * nA = 2 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_lt_trans_BAC {nB nA nC : ℕ}
    (hxy : 2 * nB < 3 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_eq_lt_BAC {nB nA nC : ℕ}
    (hxy : 2 * nB = 3 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_lt_trans_BAD {nB nA nD : ℕ}
    (hxy : 2 * nB < 3 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_eq_lt_BAD {nB nA nD : ℕ}
    (hxy : 2 * nB = 3 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_lt_trans_BAE {nB nA nE : ℕ}
    (hxy : 2 * nB < 3 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_eq_lt_BAE {nB nA nE : ℕ}
    (hxy : 2 * nB = 3 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_lt_trans_BAF {nB nA nF : ℕ}
    (hxy : 2 * nB < 3 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_eq_lt_BAF {nB nA nF : ℕ}
    (hxy : 2 * nB = 3 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_lt_trans_BAG {nB nA nG : ℕ}
    (hxy : 2 * nB < 3 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nB < 3 * nG := by omega

end QuarticExhaust810

end Max11DegreeRoutes
