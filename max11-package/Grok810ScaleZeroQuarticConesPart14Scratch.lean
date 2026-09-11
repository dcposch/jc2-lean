import Max11SpeedReflectDegLibScratch
import Fable810ScaleZeroTwelfthDefectScratch

/-! # Part 14 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_DEB {nD nE nB : ℕ}
    (hxy : 6 * nD = 5 * nE) (hyz : 3 * nE < 6 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_lt_trans_DEC {nD nE nC : ℕ}
    (hxy : 6 * nD < 5 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_eq_lt_DEC {nD nE nC : ℕ}
    (hxy : 6 * nD = 5 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_lt_trans_DEF {nD nE nF : ℕ}
    (hxy : 6 * nD < 5 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_eq_lt_DEF {nD nE nF : ℕ}
    (hxy : 6 * nD = 5 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nD < 5 * nF := by omega

theorem quarticScore_lt_trans_DEG {nD nE nG : ℕ}
    (hxy : 6 * nD < 5 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_eq_lt_DEG {nD nE nG : ℕ}
    (hxy : 6 * nD = 5 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_lt_trans_DFA {nD nF nA : ℕ}
    (hxy : 7 * nD < 5 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_eq_lt_DFA {nD nF nA : ℕ}
    (hxy : 7 * nD = 5 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_lt_trans_DFB {nD nF nB : ℕ}
    (hxy : 7 * nD < 5 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_eq_lt_DFB {nD nF nB : ℕ}
    (hxy : 7 * nD = 5 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_lt_trans_DFC {nD nF nC : ℕ}
    (hxy : 7 * nD < 5 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_eq_lt_DFC {nD nF nC : ℕ}
    (hxy : 7 * nD = 5 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_lt_trans_DFE {nD nF nE : ℕ}
    (hxy : 7 * nD < 5 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_eq_lt_DFE {nD nF nE : ℕ}
    (hxy : 7 * nD = 5 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nD < 5 * nE := by omega

theorem quarticScore_lt_trans_DFG {nD nF nG : ℕ}
    (hxy : 7 * nD < 5 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_eq_lt_DFG {nD nF nG : ℕ}
    (hxy : 7 * nD = 5 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nD < 5 * nG := by omega

theorem quarticScore_lt_trans_DGA {nD nG nA : ℕ}
    (hxy : 8 * nD < 5 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_eq_lt_DGA {nD nG nA : ℕ}
    (hxy : 8 * nD = 5 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nD < 5 * nA := by omega

theorem quarticScore_lt_trans_DGB {nD nG nB : ℕ}
    (hxy : 8 * nD < 5 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_eq_lt_DGB {nD nG nB : ℕ}
    (hxy : 8 * nD = 5 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nD < 5 * nB := by omega

theorem quarticScore_lt_trans_DGC {nD nG nC : ℕ}
    (hxy : 8 * nD < 5 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_eq_lt_DGC {nD nG nC : ℕ}
    (hxy : 8 * nD = 5 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nD < 5 * nC := by omega

theorem quarticScore_lt_trans_DGE {nD nG nE : ℕ}
    (hxy : 8 * nD < 5 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nD < 5 * nE := by omega

end QuarticExhaust810

end Max11DegreeRoutes
