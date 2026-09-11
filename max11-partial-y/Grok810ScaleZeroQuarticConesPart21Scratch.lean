import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 21 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_GCA {nG nC nA : ℕ}
    (hxy : 4 * nG = 8 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_lt_trans_GCB {nG nC nB : ℕ}
    (hxy : 4 * nG < 8 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_eq_lt_GCB {nG nC nB : ℕ}
    (hxy : 4 * nG = 8 * nC) (hyz : 3 * nC < 4 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_lt_trans_GCD {nG nC nD : ℕ}
    (hxy : 4 * nG < 8 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_eq_lt_GCD {nG nC nD : ℕ}
    (hxy : 4 * nG = 8 * nC) (hyz : 5 * nC < 4 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_lt_trans_GCE {nG nC nE : ℕ}
    (hxy : 4 * nG < 8 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_eq_lt_GCE {nG nC nE : ℕ}
    (hxy : 4 * nG = 8 * nC) (hyz : 6 * nC < 4 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_lt_trans_GCF {nG nC nF : ℕ}
    (hxy : 4 * nG < 8 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_eq_lt_GCF {nG nC nF : ℕ}
    (hxy : 4 * nG = 8 * nC) (hyz : 7 * nC < 4 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_lt_trans_GDA {nG nD nA : ℕ}
    (hxy : 5 * nG < 8 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_eq_lt_GDA {nG nD nA : ℕ}
    (hxy : 5 * nG = 8 * nD) (hyz : 2 * nD < 5 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_lt_trans_GDB {nG nD nB : ℕ}
    (hxy : 5 * nG < 8 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_eq_lt_GDB {nG nD nB : ℕ}
    (hxy : 5 * nG = 8 * nD) (hyz : 3 * nD < 5 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_lt_trans_GDC {nG nD nC : ℕ}
    (hxy : 5 * nG < 8 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_eq_lt_GDC {nG nD nC : ℕ}
    (hxy : 5 * nG = 8 * nD) (hyz : 4 * nD < 5 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_lt_trans_GDE {nG nD nE : ℕ}
    (hxy : 5 * nG < 8 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_eq_lt_GDE {nG nD nE : ℕ}
    (hxy : 5 * nG = 8 * nD) (hyz : 6 * nD < 5 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_lt_trans_GDF {nG nD nF : ℕ}
    (hxy : 5 * nG < 8 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_eq_lt_GDF {nG nD nF : ℕ}
    (hxy : 5 * nG = 8 * nD) (hyz : 7 * nD < 5 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_lt_trans_GEA {nG nE nA : ℕ}
    (hxy : 6 * nG < 8 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_eq_lt_GEA {nG nE nA : ℕ}
    (hxy : 6 * nG = 8 * nE) (hyz : 2 * nE < 6 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_lt_trans_GEB {nG nE nB : ℕ}
    (hxy : 6 * nG < 8 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_eq_lt_GEB {nG nE nB : ℕ}
    (hxy : 6 * nG = 8 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_lt_trans_GEC {nG nE nC : ℕ}
    (hxy : 6 * nG < 8 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nG < 8 * nC := by omega

end QuarticExhaust810

end Max11DegreeRoutes
