import Grok810ScaleZeroQuarticConesPart08Scratch

/-! # Part 9 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_BEC {nB nE nC : ℕ}
    (hxy : 6 * nB = 3 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_lt_trans_BED {nB nE nD : ℕ}
    (hxy : 6 * nB < 3 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_eq_lt_BED {nB nE nD : ℕ}
    (hxy : 6 * nB = 3 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_lt_trans_BEF {nB nE nF : ℕ}
    (hxy : 6 * nB < 3 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_eq_lt_BEF {nB nE nF : ℕ}
    (hxy : 6 * nB = 3 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nB < 3 * nF := by omega

theorem quarticScore_lt_trans_BEG {nB nE nG : ℕ}
    (hxy : 6 * nB < 3 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_eq_lt_BEG {nB nE nG : ℕ}
    (hxy : 6 * nB = 3 * nE) (hyz : 8 * nE < 6 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_lt_trans_BFA {nB nF nA : ℕ}
    (hxy : 7 * nB < 3 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_eq_lt_BFA {nB nF nA : ℕ}
    (hxy : 7 * nB = 3 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_lt_trans_BFC {nB nF nC : ℕ}
    (hxy : 7 * nB < 3 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_eq_lt_BFC {nB nF nC : ℕ}
    (hxy : 7 * nB = 3 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_lt_trans_BFD {nB nF nD : ℕ}
    (hxy : 7 * nB < 3 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_eq_lt_BFD {nB nF nD : ℕ}
    (hxy : 7 * nB = 3 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_lt_trans_BFE {nB nF nE : ℕ}
    (hxy : 7 * nB < 3 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_eq_lt_BFE {nB nF nE : ℕ}
    (hxy : 7 * nB = 3 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nB < 3 * nE := by omega

theorem quarticScore_lt_trans_BFG {nB nF nG : ℕ}
    (hxy : 7 * nB < 3 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_eq_lt_BFG {nB nF nG : ℕ}
    (hxy : 7 * nB = 3 * nF) (hyz : 8 * nF < 7 * nG) :
    8 * nB < 3 * nG := by omega

theorem quarticScore_lt_trans_BGA {nB nG nA : ℕ}
    (hxy : 8 * nB < 3 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_eq_lt_BGA {nB nG nA : ℕ}
    (hxy : 8 * nB = 3 * nG) (hyz : 2 * nG < 8 * nA) :
    2 * nB < 3 * nA := by omega

theorem quarticScore_lt_trans_BGC {nB nG nC : ℕ}
    (hxy : 8 * nB < 3 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_eq_lt_BGC {nB nG nC : ℕ}
    (hxy : 8 * nB = 3 * nG) (hyz : 4 * nG < 8 * nC) :
    4 * nB < 3 * nC := by omega

theorem quarticScore_lt_trans_BGD {nB nG nD : ℕ}
    (hxy : 8 * nB < 3 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_eq_lt_BGD {nB nG nD : ℕ}
    (hxy : 8 * nB = 3 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nB < 3 * nD := by omega

theorem quarticScore_lt_trans_BGE {nB nG nE : ℕ}
    (hxy : 8 * nB < 3 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nB < 3 * nE := by omega

end QuarticExhaust810

end Max11DegreeRoutes
