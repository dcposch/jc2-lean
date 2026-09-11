import Grok810ScaleZeroQuarticConesPart101Scratch

/-! # Part 20 of `Grok810ScaleZeroQuarticConesScratch`.

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

theorem quarticScore_eq_lt_FGD {nF nG nD : ℕ}
    (hxy : 8 * nF = 7 * nG) (hyz : 5 * nG < 8 * nD) :
    5 * nF < 7 * nD := by omega

theorem quarticScore_lt_trans_FGE {nF nG nE : ℕ}
    (hxy : 8 * nF < 7 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_eq_lt_FGE {nF nG nE : ℕ}
    (hxy : 8 * nF = 7 * nG) (hyz : 6 * nG < 8 * nE) :
    6 * nF < 7 * nE := by omega

theorem quarticScore_lt_trans_GAB {nG nA nB : ℕ}
    (hxy : 2 * nG < 8 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_eq_lt_GAB {nG nA nB : ℕ}
    (hxy : 2 * nG = 8 * nA) (hyz : 3 * nA < 2 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_lt_trans_GAC {nG nA nC : ℕ}
    (hxy : 2 * nG < 8 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_eq_lt_GAC {nG nA nC : ℕ}
    (hxy : 2 * nG = 8 * nA) (hyz : 4 * nA < 2 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_lt_trans_GAD {nG nA nD : ℕ}
    (hxy : 2 * nG < 8 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_eq_lt_GAD {nG nA nD : ℕ}
    (hxy : 2 * nG = 8 * nA) (hyz : 5 * nA < 2 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_lt_trans_GAE {nG nA nE : ℕ}
    (hxy : 2 * nG < 8 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_eq_lt_GAE {nG nA nE : ℕ}
    (hxy : 2 * nG = 8 * nA) (hyz : 6 * nA < 2 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_lt_trans_GAF {nG nA nF : ℕ}
    (hxy : 2 * nG < 8 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_eq_lt_GAF {nG nA nF : ℕ}
    (hxy : 2 * nG = 8 * nA) (hyz : 7 * nA < 2 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_lt_trans_GBA {nG nB nA : ℕ}
    (hxy : 3 * nG < 8 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_eq_lt_GBA {nG nB nA : ℕ}
    (hxy : 3 * nG = 8 * nB) (hyz : 2 * nB < 3 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_lt_trans_GBC {nG nB nC : ℕ}
    (hxy : 3 * nG < 8 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_eq_lt_GBC {nG nB nC : ℕ}
    (hxy : 3 * nG = 8 * nB) (hyz : 4 * nB < 3 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_lt_trans_GBD {nG nB nD : ℕ}
    (hxy : 3 * nG < 8 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_eq_lt_GBD {nG nB nD : ℕ}
    (hxy : 3 * nG = 8 * nB) (hyz : 5 * nB < 3 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_lt_trans_GBE {nG nB nE : ℕ}
    (hxy : 3 * nG < 8 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_eq_lt_GBE {nG nB nE : ℕ}
    (hxy : 3 * nG = 8 * nB) (hyz : 6 * nB < 3 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_lt_trans_GBF {nG nB nF : ℕ}
    (hxy : 3 * nG < 8 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_eq_lt_GBF {nG nB nF : ℕ}
    (hxy : 3 * nG = 8 * nB) (hyz : 7 * nB < 3 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_lt_trans_GCA {nG nC nA : ℕ}
    (hxy : 4 * nG < 8 * nC) (hyz : 2 * nC < 4 * nA) :
    2 * nG < 8 * nA := by omega

end QuarticExhaust810

end Max11DegreeRoutes
