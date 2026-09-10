import Grok810ScaleZeroQuarticConesPart14Scratch

/-! # Part 15 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_DGE {nD nG nE : ℕ}
    (hxy : 8 * nD = 5 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_lt_trans_DGF {nD nG nF : ℕ}
    (hxy : 8 * nD < 5 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_eq_lt_DGF {nD nG nF : ℕ}
    (hxy : 8 * nD = 5 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_lt_trans_EAB {nE nA nB : ℕ}
    (hxy : 2 * nE < 6 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_eq_lt_EAB {nE nA nB : ℕ}
    (hxy : 2 * nE = 6 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_lt_trans_EAC {nE nA nC : ℕ}
    (hxy : 2 * nE < 6 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_eq_lt_EAC {nE nA nC : ℕ}
    (hxy : 2 * nE = 6 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_lt_trans_EAD {nE nA nD : ℕ}
    (hxy : 2 * nE < 6 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_eq_lt_EAD {nE nA nD : ℕ}
    (hxy : 2 * nE = 6 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_lt_trans_EAF {nE nA nF : ℕ}
    (hxy : 2 * nE < 6 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_eq_lt_EAF {nE nA nF : ℕ}
    (hxy : 2 * nE = 6 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_lt_trans_EAG {nE nA nG : ℕ}
    (hxy : 2 * nE < 6 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_eq_lt_EAG {nE nA nG : ℕ}
    (hxy : 2 * nE = 6 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_lt_trans_EBA {nE nB nA : ℕ}
    (hxy : 3 * nE < 6 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_eq_lt_EBA {nE nB nA : ℕ}
    (hxy : 3 * nE = 6 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_lt_trans_EBC {nE nB nC : ℕ}
    (hxy : 3 * nE < 6 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_eq_lt_EBC {nE nB nC : ℕ}
    (hxy : 3 * nE = 6 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_lt_trans_EBD {nE nB nD : ℕ}
    (hxy : 3 * nE < 6 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_eq_lt_EBD {nE nB nD : ℕ}
    (hxy : 3 * nE = 6 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_lt_trans_EBF {nE nB nF : ℕ}
    (hxy : 3 * nE < 6 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_eq_lt_EBF {nE nB nF : ℕ}
    (hxy : 3 * nE = 6 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_lt_trans_EBG {nE nB nG : ℕ}
    (hxy : 3 * nE < 6 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_eq_lt_EBG {nE nB nG : ℕ}
    (hxy : 3 * nE = 6 * nB) (hyz : 8 * nB < 3 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_lt_trans_ECA {nE nC nA : ℕ}
    (hxy : 4 * nE < 6 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nE < 6 * nA := by omega

end QuarticExhaust810

end Max11DegreeRoutes
