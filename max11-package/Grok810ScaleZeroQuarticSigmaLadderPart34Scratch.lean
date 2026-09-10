import Grok810ScaleZeroQuarticSigmaLadderPart33Scratch

/-! Part 34 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

variable {k : Type*} [Field k] [CharZero k]

section QuarticSigmaSupportCones810


set_option maxHeartbeats 64000000 in
/-- Residual chamber of the σ-defect taxonomy: `C` wins the
singleton-face race (`3σ_C ≤ k_Z σ_Z` for every live `Z`) yet the mixed
monomial `C·G` is strictly cheaper than `C³` (`σ_G < 2σ_C`), so the
cost minimum is the single monomial `CG`, which is not the face of any of
the 63 `QuarticSigmaSupportCone810` constructors.  See the emitter
`scripts/emit_810_quartic_sigma_exhaust.py`. -/
def QuarticMixedSigmaConeCG810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    C ≠ 0 ∧
    G ≠ 0 ∧
    2 * C.natDegree < G.natDegree ∧
    2 * G.natDegree ≤ 2 * A.natDegree + 3 * C.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree ≤ 2 * C.natDegree) ∧
    (D = 0 ∨ A.natDegree + 2 * D.natDegree ≤ 3 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree ≤ 3 * C.natDegree) ∧
    (F = 0 ∨ 2 * F.natDegree ≤ A.natDegree + 3 * C.natDegree)


set_option maxHeartbeats 64000000 in
inductive QuarticSigmaSupportCone810 (A B C D E F G : k[X]) : Prop
  | sigmaB : QuarticSigmaConeB810' A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaC : QuarticSigmaConeC810' A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaD : QuarticLoadSigmaConeD810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaE : QuarticLoadSigmaConeE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaF : QuarticLoadSigmaConeF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaG : QuarticLoadSigmaConeG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBC : QuarticSigmaConeBC810' A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBD : QuarticLoadSigmaConeBD810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBE : QuarticLoadSigmaConeBE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBF : QuarticLoadSigmaConeBF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBG : QuarticLoadSigmaConeBG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCD : QuarticLoadSigmaConeCD810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCE : QuarticLoadSigmaConeCE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCF : QuarticLoadSigmaConeCF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCG : QuarticLoadSigmaConeCG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDE : QuarticLoadSigmaConeDE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDF : QuarticLoadSigmaConeDF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDG : QuarticLoadSigmaConeDG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaEF : QuarticLoadSigmaConeEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaEG : QuarticLoadSigmaConeEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaFG : QuarticLoadSigmaConeFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCD : QuarticLoadSigmaConeBCD810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCE : QuarticLoadSigmaConeBCE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCF : QuarticLoadSigmaConeBCF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCG : QuarticLoadSigmaConeBCG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDE : QuarticLoadSigmaConeBDE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDF : QuarticLoadSigmaConeBDF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDG : QuarticLoadSigmaConeBDG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBEF : QuarticLoadSigmaConeBEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBEG : QuarticLoadSigmaConeBEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBFG : QuarticLoadSigmaConeBFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDE : QuarticLoadSigmaConeCDE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDF : QuarticLoadSigmaConeCDF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDG : QuarticLoadSigmaConeCDG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCEF : QuarticLoadSigmaConeCEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCEG : QuarticLoadSigmaConeCEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCFG : QuarticLoadSigmaConeCFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDEF : QuarticLoadSigmaConeDEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDEG : QuarticLoadSigmaConeDEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDFG : QuarticLoadSigmaConeDFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaEFG : QuarticLoadSigmaConeEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDE : QuarticLoadSigmaConeBCDE810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDF : QuarticLoadSigmaConeBCDF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDG : QuarticLoadSigmaConeBCDG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCEF : QuarticLoadSigmaConeBCEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCEG : QuarticLoadSigmaConeBCEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCFG : QuarticLoadSigmaConeBCFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDEF : QuarticLoadSigmaConeBDEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDEG : QuarticLoadSigmaConeBDEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDFG : QuarticLoadSigmaConeBDFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBEFG : QuarticLoadSigmaConeBEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDEF : QuarticLoadSigmaConeCDEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDEG : QuarticLoadSigmaConeCDEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDFG : QuarticLoadSigmaConeCDFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCEFG : QuarticLoadSigmaConeCEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaDEFG : QuarticLoadSigmaConeDEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDEF : QuarticLoadSigmaConeBCDEF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDEG : QuarticLoadSigmaConeBCDEG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDFG : QuarticLoadSigmaConeBCDFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCEFG : QuarticLoadSigmaConeBCEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBDEFG : QuarticLoadSigmaConeBDEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaCDEFG : QuarticLoadSigmaConeCDEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | sigmaBCDEFG : QuarticLoadSigmaConeBCDEFG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | mixedBF : QuarticMixedSigmaConeBF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | mixedBG : QuarticMixedSigmaConeBG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | mixedCF : QuarticMixedSigmaConeCF810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G
  | mixedCG : QuarticMixedSigmaConeCG810 A B C D E F G →
      QuarticSigmaSupportCone810 A B C D E F G


end QuarticSigmaSupportCones810
end Max11DegreeRoutes
end
