import Grok810ScaleZeroQuarticConesPart17Scratch

/-! # Part 18 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_FAG {nF nA nG : ℕ}
    (hxy : 2 * nF = 7 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_lt_trans_FBA {nF nB nA : ℕ}
    (hxy : 3 * nF < 7 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_eq_lt_FBA {nF nB nA : ℕ}
    (hxy : 3 * nF = 7 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_lt_trans_FBC {nF nB nC : ℕ}
    (hxy : 3 * nF < 7 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_eq_lt_FBC {nF nB nC : ℕ}
    (hxy : 3 * nF = 7 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_lt_trans_FBD {nF nB nD : ℕ}
    (hxy : 3 * nF < 7 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_eq_lt_FBD {nF nB nD : ℕ}
    (hxy : 3 * nF = 7 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_lt_trans_FBE {nF nB nE : ℕ}
    (hxy : 3 * nF < 7 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_eq_lt_FBE {nF nB nE : ℕ}
    (hxy : 3 * nF = 7 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_lt_trans_FBG {nF nB nG : ℕ}
    (hxy : 3 * nF < 7 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_eq_lt_FBG {nF nB nG : ℕ}
    (hxy : 3 * nF = 7 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_lt_trans_FCA {nF nC nA : ℕ}
    (hxy : 4 * nF < 7 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_eq_lt_FCA {nF nC nA : ℕ}
    (hxy : 4 * nF = 7 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_lt_trans_FCB {nF nC nB : ℕ}
    (hxy : 4 * nF < 7 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_eq_lt_FCB {nF nC nB : ℕ}
    (hxy : 4 * nF = 7 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_lt_trans_FCD {nF nC nD : ℕ}
    (hxy : 4 * nF < 7 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_eq_lt_FCD {nF nC nD : ℕ}
    (hxy : 4 * nF = 7 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_lt_trans_FCE {nF nC nE : ℕ}
    (hxy : 4 * nF < 7 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_eq_lt_FCE {nF nC nE : ℕ}
    (hxy : 4 * nF = 7 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_lt_trans_FCG {nF nC nG : ℕ}
    (hxy : 4 * nF < 7 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_eq_lt_FCG {nF nC nG : ℕ}
    (hxy : 4 * nF = 7 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nF < 7 * nG := by omega

theorem quarticScore_lt_trans_FDA {nF nD nA : ℕ}
    (hxy : 5 * nF < 7 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_eq_lt_FDA {nF nD nA : ℕ}
    (hxy : 5 * nF = 7 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nF < 7 * nA := by omega

theorem quarticScore_lt_trans_FDB {nF nD nB : ℕ}
    (hxy : 5 * nF < 7 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nF < 7 * nB := by omega

end QuarticExhaust810

end Max11DegreeRoutes
