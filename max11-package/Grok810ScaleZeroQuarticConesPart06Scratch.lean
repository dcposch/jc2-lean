import Grok810ScaleZeroQuarticConesPart05Scratch

/-! # Part 6 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_ADB {nA nD nB : ℕ}
    (hxy : 5 * nA = 2 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_lt_trans_ADC {nA nD nC : ℕ}
    (hxy : 5 * nA < 2 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_eq_lt_ADC {nA nD nC : ℕ}
    (hxy : 5 * nA = 2 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_lt_trans_ADE {nA nD nE : ℕ}
    (hxy : 5 * nA < 2 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_eq_lt_ADE {nA nD nE : ℕ}
    (hxy : 5 * nA = 2 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nA < 2 * nE := by omega

theorem quarticScore_lt_trans_ADF {nA nD nF : ℕ}
    (hxy : 5 * nA < 2 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_eq_lt_ADF {nA nD nF : ℕ}
    (hxy : 5 * nA = 2 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_lt_trans_ADG {nA nD nG : ℕ}
    (hxy : 5 * nA < 2 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_eq_lt_ADG {nA nD nG : ℕ}
    (hxy : 5 * nA = 2 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_lt_trans_AEB {nA nE nB : ℕ}
    (hxy : 6 * nA < 2 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_eq_lt_AEB {nA nE nB : ℕ}
    (hxy : 6 * nA = 2 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_lt_trans_AEC {nA nE nC : ℕ}
    (hxy : 6 * nA < 2 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_eq_lt_AEC {nA nE nC : ℕ}
    (hxy : 6 * nA = 2 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_lt_trans_AED {nA nE nD : ℕ}
    (hxy : 6 * nA < 2 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_eq_lt_AED {nA nE nD : ℕ}
    (hxy : 6 * nA = 2 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nA < 2 * nD := by omega

theorem quarticScore_lt_trans_AEF {nA nE nF : ℕ}
    (hxy : 6 * nA < 2 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_eq_lt_AEF {nA nE nF : ℕ}
    (hxy : 6 * nA = 2 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nA < 2 * nF := by omega

theorem quarticScore_lt_trans_AEG {nA nE nG : ℕ}
    (hxy : 6 * nA < 2 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_eq_lt_AEG {nA nE nG : ℕ}
    (hxy : 6 * nA = 2 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nA < 2 * nG := by omega

theorem quarticScore_lt_trans_AFB {nA nF nB : ℕ}
    (hxy : 7 * nA < 2 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_eq_lt_AFB {nA nF nB : ℕ}
    (hxy : 7 * nA = 2 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nA < 2 * nB := by omega

theorem quarticScore_lt_trans_AFC {nA nF nC : ℕ}
    (hxy : 7 * nA < 2 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_eq_lt_AFC {nA nF nC : ℕ}
    (hxy : 7 * nA = 2 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nA < 2 * nC := by omega

theorem quarticScore_lt_trans_AFD {nA nF nD : ℕ}
    (hxy : 7 * nA < 2 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nA < 2 * nD := by omega

end QuarticExhaust810

end Max11DegreeRoutes
