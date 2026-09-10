import Grok810ScaleZeroQuarticConesPart16Scratch

/-! # Part 17 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_EFC {nE nF nC : ℕ}
    (hxy : 7 * nE = 6 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_lt_trans_EFD {nE nF nD : ℕ}
    (hxy : 7 * nE < 6 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_eq_lt_EFD {nE nF nD : ℕ}
    (hxy : 7 * nE = 6 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_lt_trans_EFG {nE nF nG : ℕ}
    (hxy : 7 * nE < 6 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_eq_lt_EFG {nE nF nG : ℕ}
    (hxy : 7 * nE = 6 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nE < 6 * nG := by omega

theorem quarticScore_lt_trans_EGA {nE nG nA : ℕ}
    (hxy : 8 * nE < 6 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_eq_lt_EGA {nE nG nA : ℕ}
    (hxy : 8 * nE = 6 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nE < 6 * nA := by omega

theorem quarticScore_lt_trans_EGB {nE nG nB : ℕ}
    (hxy : 8 * nE < 6 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_eq_lt_EGB {nE nG nB : ℕ}
    (hxy : 8 * nE = 6 * nG) (hyz : 3 * nG < 8 * nB) :
    3 * nE < 6 * nB := by omega

theorem quarticScore_lt_trans_EGC {nE nG nC : ℕ}
    (hxy : 8 * nE < 6 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_eq_lt_EGC {nE nG nC : ℕ}
    (hxy : 8 * nE = 6 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nE < 6 * nC := by omega

theorem quarticScore_lt_trans_EGD {nE nG nD : ℕ}
    (hxy : 8 * nE < 6 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_eq_lt_EGD {nE nG nD : ℕ}
    (hxy : 8 * nE = 6 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nE < 6 * nD := by omega

theorem quarticScore_lt_trans_EGF {nE nG nF : ℕ}
    (hxy : 8 * nE < 6 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_eq_lt_EGF {nE nG nF : ℕ}
    (hxy : 8 * nE = 6 * nG) (hyz : 7 * nG < 8 * nF) :
    7 * nE < 6 * nF := by omega

theorem quarticScore_lt_trans_FAB {nF nA nB : ℕ}
    (hxy : 2 * nF < 7 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_eq_lt_FAB {nF nA nB : ℕ}
    (hxy : 2 * nF = 7 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nF < 7 * nB := by omega

theorem quarticScore_lt_trans_FAC {nF nA nC : ℕ}
    (hxy : 2 * nF < 7 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_eq_lt_FAC {nF nA nC : ℕ}
    (hxy : 2 * nF = 7 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nF < 7 * nC := by omega

theorem quarticScore_lt_trans_FAD {nF nA nD : ℕ}
    (hxy : 2 * nF < 7 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_eq_lt_FAD {nF nA nD : ℕ}
    (hxy : 2 * nF = 7 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_lt_trans_FAE {nF nA nE : ℕ}
    (hxy : 2 * nF < 7 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_eq_lt_FAE {nF nA nE : ℕ}
    (hxy : 2 * nF = 7 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_lt_trans_FAG {nF nA nG : ℕ}
    (hxy : 2 * nF < 7 * nA) (hyz : 8 * nA < 2 * nG) :
    8 * nF < 7 * nG := by omega

end QuarticExhaust810

end Max11DegreeRoutes
