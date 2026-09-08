import Grok810ScaleZeroQuarticConesPart15Scratch

/-! # Part 16 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_ECA {nE nC nA : ℕ}
    (hxy : 4 * nE = 6 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_lt_trans_ECB {nE nC nB : ℕ}
    (hxy : 4 * nE < 6 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_eq_lt_ECB {nE nC nB : ℕ}
    (hxy : 4 * nE = 6 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_lt_trans_ECD {nE nC nD : ℕ}
    (hxy : 4 * nE < 6 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_eq_lt_ECD {nE nC nD : ℕ}
    (hxy : 4 * nE = 6 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_lt_trans_ECF {nE nC nF : ℕ}
    (hxy : 4 * nE < 6 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_eq_lt_ECF {nE nC nF : ℕ}
    (hxy : 4 * nE = 6 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_lt_trans_ECG {nE nC nG : ℕ}
    (hxy : 4 * nE < 6 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_eq_lt_ECG {nE nC nG : ℕ}
    (hxy : 4 * nE = 6 * nC) (hyz : 8 * nC < 4 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_lt_trans_EDA {nE nD nA : ℕ}
    (hxy : 5 * nE < 6 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_eq_lt_EDA {nE nD nA : ℕ}
    (hxy : 5 * nE = 6 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_lt_trans_EDB {nE nD nB : ℕ}
    (hxy : 5 * nE < 6 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_eq_lt_EDB {nE nD nB : ℕ}
    (hxy : 5 * nE = 6 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_lt_trans_EDC {nE nD nC : ℕ}
    (hxy : 5 * nE < 6 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_eq_lt_EDC {nE nD nC : ℕ}
    (hxy : 5 * nE = 6 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_lt_trans_EDF {nE nD nF : ℕ}
    (hxy : 5 * nE < 6 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_eq_lt_EDF {nE nD nF : ℕ}
    (hxy : 5 * nE = 6 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_lt_trans_EDG {nE nD nG : ℕ}
    (hxy : 5 * nE < 6 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_eq_lt_EDG {nE nD nG : ℕ}
    (hxy : 5 * nE = 6 * nD) (hyz : 8 * nD < 5 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_lt_trans_EFA {nE nF nA : ℕ}
    (hxy : 7 * nE < 6 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_eq_lt_EFA {nE nF nA : ℕ}
    (hxy : 7 * nE = 6 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_lt_trans_EFB {nE nF nB : ℕ}
    (hxy : 7 * nE < 6 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_eq_lt_EFB {nE nF nB : ℕ}
    (hxy : 7 * nE = 6 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_lt_trans_EFC {nE nF nC : ℕ}
    (hxy : 7 * nE < 6 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nE < 6 * nC := by omega

end QuarticExhaust810

end Max11DegreeRoutes
