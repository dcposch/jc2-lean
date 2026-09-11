import Grok810ScaleZeroQuarticDefsScratch

/-! # Part 1 of `Grok810ScaleZeroQuarticConesScratch`.

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

inductive QuarticSupportCone810 (A B C D E F G : k[X]) : Prop
  | coneA : QuarticRatioConeA810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneB : QuarticRatioConeB810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneC : QuarticRatioConeC810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneD : QuarticRatioConeD810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneE : QuarticRatioConeE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneF : QuarticRatioConeF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneG : QuarticRatioConeG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAB : QuarticRatioConeAB810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAC : QuarticRatioConeAC810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAD : QuarticRatioConeAD810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAE : QuarticRatioConeAE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAF : QuarticRatioConeAF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAG : QuarticRatioConeAG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBC : QuarticRatioConeBC810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBD : QuarticRatioConeBD810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBE : QuarticRatioConeBE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBF : QuarticRatioConeBF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBG : QuarticRatioConeBG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCD : QuarticRatioConeCD810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCE : QuarticRatioConeCE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCF : QuarticRatioConeCF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCG : QuarticRatioConeCG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneDE : QuarticRatioConeDE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneDF : QuarticRatioConeDF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneDG : QuarticRatioConeDG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneEF : QuarticRatioConeEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneEG : QuarticRatioConeEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneFG : QuarticRatioConeFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABC : QuarticRatioConeABC810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABD : QuarticRatioConeABD810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABE : QuarticRatioConeABE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABF : QuarticRatioConeABF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABG : QuarticRatioConeABG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACD : QuarticRatioConeACD810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACE : QuarticRatioConeACE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACF : QuarticRatioConeACF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACG : QuarticRatioConeACG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneADE : QuarticRatioConeADE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneADF : QuarticRatioConeADF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneADG : QuarticRatioConeADG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAEF : QuarticRatioConeAEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAEG : QuarticRatioConeAEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAFG : QuarticRatioConeAFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCD : QuarticRatioConeBCD810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCE : QuarticRatioConeBCE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCF : QuarticRatioConeBCF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCG : QuarticRatioConeBCG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBDE : QuarticRatioConeBDE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBDF : QuarticRatioConeBDF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBDG : QuarticRatioConeBDG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBEF : QuarticRatioConeBEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBEG : QuarticRatioConeBEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBFG : QuarticRatioConeBFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCDE : QuarticRatioConeCDE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCDF : QuarticRatioConeCDF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCDG : QuarticRatioConeCDG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCEF : QuarticRatioConeCEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCEG : QuarticRatioConeCEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCFG : QuarticRatioConeCFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneDEF : QuarticRatioConeDEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneDEG : QuarticRatioConeDEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneDFG : QuarticRatioConeDFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneEFG : QuarticRatioConeEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCD : QuarticRatioConeABCD810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCE : QuarticRatioConeABCE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCF : QuarticRatioConeABCF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCG : QuarticRatioConeABCG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABDE : QuarticRatioConeABDE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABDF : QuarticRatioConeABDF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABDG : QuarticRatioConeABDG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABEF : QuarticRatioConeABEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABEG : QuarticRatioConeABEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABFG : QuarticRatioConeABFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACDE : QuarticRatioConeACDE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACDF : QuarticRatioConeACDF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACDG : QuarticRatioConeACDG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACEF : QuarticRatioConeACEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACEG : QuarticRatioConeACEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACFG : QuarticRatioConeACFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneADEF : QuarticRatioConeADEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneADEG : QuarticRatioConeADEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneADFG : QuarticRatioConeADFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneAEFG : QuarticRatioConeAEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCDE : QuarticRatioConeBCDE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCDF : QuarticRatioConeBCDF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCDG : QuarticRatioConeBCDG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCEF : QuarticRatioConeBCEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCEG : QuarticRatioConeBCEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCFG : QuarticRatioConeBCFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBDEF : QuarticRatioConeBDEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBDEG : QuarticRatioConeBDEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBDFG : QuarticRatioConeBDFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBEFG : QuarticRatioConeBEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCDEF : QuarticRatioConeCDEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCDEG : QuarticRatioConeCDEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCDFG : QuarticRatioConeCDFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCEFG : QuarticRatioConeCEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneDEFG : QuarticRatioConeDEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCDE : QuarticRatioConeABCDE810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCDF : QuarticRatioConeABCDF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCDG : QuarticRatioConeABCDG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCEF : QuarticRatioConeABCEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCEG : QuarticRatioConeABCEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCFG : QuarticRatioConeABCFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABDEF : QuarticRatioConeABDEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABDEG : QuarticRatioConeABDEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABDFG : QuarticRatioConeABDFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABEFG : QuarticRatioConeABEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACDEF : QuarticRatioConeACDEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACDEG : QuarticRatioConeACDEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACDFG : QuarticRatioConeACDFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACEFG : QuarticRatioConeACEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneADEFG : QuarticRatioConeADEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCDEF : QuarticRatioConeBCDEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCDEG : QuarticRatioConeBCDEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCDFG : QuarticRatioConeBCDFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCEFG : QuarticRatioConeBCEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBDEFG : QuarticRatioConeBDEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneCDEFG : QuarticRatioConeCDEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCDEF : QuarticRatioConeABCDEF810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCDEG : QuarticRatioConeABCDEG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCDFG : QuarticRatioConeABCDFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCEFG : QuarticRatioConeABCEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABDEFG : QuarticRatioConeABDEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneACDEFG : QuarticRatioConeACDEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneBCDEFG : QuarticRatioConeBCDEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | coneABCDEFG : QuarticRatioConeABCDEFG810 A B C D E F G →
      QuarticSupportCone810 A B C D E F G
  | allConst : A.natDegree = 0 ∧ B.natDegree = 0 ∧ C.natDegree = 0 ∧
      D.natDegree = 0 ∧ E.natDegree = 0 ∧ F.natDegree = 0 ∧
      G.natDegree = 0 → QuarticSupportCone810 A B C D E F G

/-! Score helpers: each `omega` sees at most three linear Nat facts. -/

theorem quarticScore_not_lt_not_eq {a b : ℕ}
    (hnlt : ¬ a < b) (hneq : ¬ a = b) : b < a := by omega

theorem quarticCmp_AC_of_raw {nA nC : ℕ}
    (h : 4 * nA < 2 * nC) : 2 * nA < nC := by omega

theorem quarticCmp_AC_to_raw {nA nC : ℕ}
    (h : 2 * nA < nC) : 4 * nA < 2 * nC := by omega

theorem quarticEq_AC_of_raw {nA nC : ℕ}
    (h : 4 * nA = 2 * nC) : 2 * nA = nC := by omega

theorem quarticEq_AC_to_raw {nA nC : ℕ}
    (h : 2 * nA = nC) : 4 * nA = 2 * nC := by omega

theorem quarticCmp_AE_of_raw {nA nE : ℕ}
    (h : 6 * nA < 2 * nE) : 3 * nA < nE := by omega

theorem quarticCmp_AE_to_raw {nA nE : ℕ}
    (h : 3 * nA < nE) : 6 * nA < 2 * nE := by omega

theorem quarticEq_AE_of_raw {nA nE : ℕ}
    (h : 6 * nA = 2 * nE) : 3 * nA = nE := by omega

theorem quarticEq_AE_to_raw {nA nE : ℕ}
    (h : 3 * nA = nE) : 6 * nA = 2 * nE := by omega

theorem quarticCmp_AG_of_raw {nA nG : ℕ}
    (h : 8 * nA < 2 * nG) : 4 * nA < nG := by omega

theorem quarticCmp_AG_to_raw {nA nG : ℕ}
    (h : 4 * nA < nG) : 8 * nA < 2 * nG := by omega

theorem quarticEq_AG_of_raw {nA nG : ℕ}
    (h : 8 * nA = 2 * nG) : 4 * nA = nG := by omega

theorem quarticEq_AG_to_raw {nA nG : ℕ}
    (h : 4 * nA = nG) : 8 * nA = 2 * nG := by omega

theorem quarticCmp_BE_of_raw {nB nE : ℕ}
    (h : 6 * nB < 3 * nE) : 2 * nB < nE := by omega

theorem quarticCmp_BE_to_raw {nB nE : ℕ}
    (h : 2 * nB < nE) : 6 * nB < 3 * nE := by omega

theorem quarticEq_BE_of_raw {nB nE : ℕ}
    (h : 6 * nB = 3 * nE) : 2 * nB = nE := by omega

theorem quarticEq_BE_to_raw {nB nE : ℕ}
    (h : 2 * nB = nE) : 6 * nB = 3 * nE := by omega

theorem quarticCmp_CA_of_raw {nC nA : ℕ}
    (h : 2 * nC < 4 * nA) : nC < 2 * nA := by omega

theorem quarticCmp_CA_to_raw {nC nA : ℕ}
    (h : nC < 2 * nA) : 2 * nC < 4 * nA := by omega

theorem quarticEq_CA_of_raw {nC nA : ℕ}
    (h : 2 * nC = 4 * nA) : nC = 2 * nA := by omega

theorem quarticEq_CA_to_raw {nC nA : ℕ}
    (h : nC = 2 * nA) : 2 * nC = 4 * nA := by omega

theorem quarticCmp_CE_of_raw {nC nE : ℕ}
    (h : 6 * nC < 4 * nE) : 3 * nC < 2 * nE := by omega

theorem quarticCmp_CE_to_raw {nC nE : ℕ}
    (h : 3 * nC < 2 * nE) : 6 * nC < 4 * nE := by omega

theorem quarticEq_CE_of_raw {nC nE : ℕ}
    (h : 6 * nC = 4 * nE) : 3 * nC = 2 * nE := by omega

end QuarticExhaust810

end Max11DegreeRoutes
