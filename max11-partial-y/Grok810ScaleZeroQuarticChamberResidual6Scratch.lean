import Grok810ScaleZeroQuarticChamberExhaust4Part105Scratch
import Grok810ScaleZeroQuarticChamberRefinedKillsScratch
import Grok810ScaleZeroQuarticChamberExhaust4Part106Scratch

/-! # The last chamber residual, `(8,10)` scale zero

`QuarticChamberResidual6810` (135 whole chambers + 37 refined leaves)
and `normalized810ScaleZero_quarticChamber6Residual`.  Untracked working note.
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

variable {k : Type*} [Field k] [CharZero k]

section QuarticChamberResidual6810

variable [IsAlgClosed k]

/-! ## The last chamber residual -/

set_option maxHeartbeats 64000000 in
/-- The 135 whole chambers and 37 refined leaves
no kill module reaches. -/
inductive QuarticChamberResidual6810 (A B C D E F G : k[X]) : Prop
  | rC0 : QuarticChamberC0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rE0 : QuarticChamberE0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rG0 : QuarticChamberG0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBG2 : QuarticChamberBG2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCD2 : QuarticChamberCD2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCE2 : QuarticChamberCE2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCF1 : QuarticChamberCF1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCG1 : QuarticChamberCG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCG2 : QuarticChamberCG2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDG0 : QuarticChamberDG0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rEF0 : QuarticChamberEF0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rEG0 : QuarticChamberEG0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rFG0 : QuarticChamberFG0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rFG1 : QuarticChamberFG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCD6 : QuarticChamberBCD6810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCF5 : QuarticChamberBCF5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCG3 : QuarticChamberBCG3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCG5 : QuarticChamberBCG5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCG10 : QuarticChamberBCG10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBDF3 : QuarticChamberBDF3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBDG2 : QuarticChamberBDG2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBEF3 : QuarticChamberBEF3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBFG8 : QuarticChamberBFG8810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDE2 : QuarticChamberCDE2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDE6 : QuarticChamberCDE6810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDF1 : QuarticChamberCDF1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDF8 : QuarticChamberCDF8810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDG1 : QuarticChamberCDG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDG2 : QuarticChamberCDG2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDG3 : QuarticChamberCDG3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDG4 : QuarticChamberCDG4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDG8 : QuarticChamberCDG8810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEF1 : QuarticChamberCEF1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEF8 : QuarticChamberCEF8810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEG1 : QuarticChamberCEG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEG2 : QuarticChamberCEG2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEG4 : QuarticChamberCEG4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCFG1 : QuarticChamberCFG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCFG3 : QuarticChamberCFG3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCFG7 : QuarticChamberCFG7810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCFG8 : QuarticChamberCFG8810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEF2 : QuarticChamberDEF2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEG0 : QuarticChamberDEG0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEG4 : QuarticChamberDEG4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDFG0 : QuarticChamberDFG0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDFG1 : QuarticChamberDFG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rEFG0 : QuarticChamberEFG0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rEFG1 : QuarticChamberEFG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDG16 : QuarticChamberBCDG16810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDG17 : QuarticChamberBCDG17810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDG18 : QuarticChamberBCDG18810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDG24 : QuarticChamberBCDG24810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCFG7 : QuarticChamberBCFG7810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCFG11 : QuarticChamberBCFG11810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCFG15 : QuarticChamberBCFG15810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCFG17 : QuarticChamberBCFG17810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBDFG7 : QuarticChamberBDFG7810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBEFG7 : QuarticChamberBEFG7810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEF1 : QuarticChamberCDEF1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEG1 : QuarticChamberCDEG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEG2 : QuarticChamberCDEG2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEG3 : QuarticChamberCDEG3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEG4 : QuarticChamberCDEG4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEG9 : QuarticChamberCDEG9810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEG10 : QuarticChamberCDEG10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEG14 : QuarticChamberCDEG14810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEG20 : QuarticChamberCDEG20810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG1 : QuarticChamberCDFG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG3 : QuarticChamberCDFG3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG5 : QuarticChamberCDFG5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG7 : QuarticChamberCDFG7810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG13 : QuarticChamberCDFG13810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG14 : QuarticChamberCDFG14810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG15 : QuarticChamberCDFG15810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG16 : QuarticChamberCDFG16810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDFG20 : QuarticChamberCDFG20810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG1 : QuarticChamberCEFG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG3 : QuarticChamberCEFG3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG5 : QuarticChamberCEFG5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG7 : QuarticChamberCEFG7810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG13 : QuarticChamberCEFG13810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG14 : QuarticChamberCEFG14810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG15 : QuarticChamberCEFG15810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG16 : QuarticChamberCEFG16810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCEFG20 : QuarticChamberCEFG20810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEFG0 : QuarticChamberDEFG0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEFG1 : QuarticChamberDEFG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEFG4 : QuarticChamberDEFG4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEFG5 : QuarticChamberDEFG5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEFG8 : QuarticChamberDEFG8810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rDEFG9 : QuarticChamberDEFG9810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEF10 : QuarticChamberBCDEF10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEG10 : QuarticChamberBCDEG10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG9 : QuarticChamberBCDFG9810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG10 : QuarticChamberBCDFG10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG14 : QuarticChamberBCDFG14810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG45 : QuarticChamberBCDFG45810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCEFG9 : QuarticChamberBCEFG9810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCEFG10 : QuarticChamberBCEFG10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCEFG14 : QuarticChamberBCEFG14810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCEFG45 : QuarticChamberBCEFG45810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBDEFG7 : QuarticChamberBDEFG7810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBDEFG9 : QuarticChamberBDEFG9810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBDEFG10 : QuarticChamberBDEFG10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBDEFG13 : QuarticChamberBDEFG13810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBDEFG39 : QuarticChamberBDEFG39810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG1 : QuarticChamberCDEFG1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG3 : QuarticChamberCDEFG3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG5 : QuarticChamberCDEFG5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG7 : QuarticChamberCDEFG7810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG8 : QuarticChamberCDEFG8810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG9 : QuarticChamberCDEFG9810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG10 : QuarticChamberCDEFG10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG11 : QuarticChamberCDEFG11810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG13 : QuarticChamberCDEFG13810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG25 : QuarticChamberCDEFG25810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG39 : QuarticChamberCDEFG39810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG9 : QuarticChamberBCDEFG9810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG10 : QuarticChamberBCDEFG10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG11 : QuarticChamberBCDEFG11810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG12 : QuarticChamberBCDEFG12810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG13 : QuarticChamberBCDEFG13810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG15 : QuarticChamberBCDEFG15810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG16 : QuarticChamberBCDEFG16810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG20 : QuarticChamberBCDEFG20810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG22 : QuarticChamberBCDEFG22810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG23 : QuarticChamberBCDEFG23810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG26 : QuarticChamberBCDEFG26810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG34 : QuarticChamberBCDEFG34810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG58 : QuarticChamberBCDEFG58810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG81 : QuarticChamberBCDEFG81810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG83 : QuarticChamberBCDEFG83810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG84 : QuarticChamberBCDEFG84810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG87 : QuarticChamberBCDEFG87810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG115 : QuarticChamberBCDEFG115810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEG30L0 : QuarticRefinedBCDEG30L0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEG30L2 : QuarticRefinedBCDEG30L2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEG30L3 : QuarticRefinedBCDEG30L3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEG30L4 : QuarticRefinedBCDEG30L4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEG36L0 : QuarticRefinedBCDEG36L0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG7L1 : QuarticRefinedBCDFG7L1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG7L2 : QuarticRefinedBCDFG7L2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG54L0 : QuarticRefinedBCDFG54L0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG54L3 : QuarticRefinedBCDFG54L3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDFG54L4 : QuarticRefinedBCDFG54L4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCEFG7L1 : QuarticRefinedBCEFG7L1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCEFG7L2 : QuarticRefinedBCEFG7L2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCEFG54L0 : QuarticRefinedBCEFG54L0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG28L0 : QuarticRefinedCDEFG28L0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG28L3 : QuarticRefinedCDEFG28L3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG28L4 : QuarticRefinedCDEFG28L4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG34L0 : QuarticRefinedCDEFG34L0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG34L1 : QuarticRefinedCDEFG34L1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rCDEFG34L2 : QuarticRefinedCDEFG34L2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG7L1 : QuarticRefinedBCDEFG7L1810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG7L2 : QuarticRefinedBCDEFG7L2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG7L3 : QuarticRefinedBCDEFG7L3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG7L5 : QuarticRefinedBCDEFG7L5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG7L6 : QuarticRefinedBCDEFG7L6810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L0 : QuarticRefinedBCDEFG102L0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L2 : QuarticRefinedBCDEFG102L2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L3 : QuarticRefinedBCDEFG102L3810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L4 : QuarticRefinedBCDEFG102L4810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L5 : QuarticRefinedBCDEFG102L5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L8 : QuarticRefinedBCDEFG102L8810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L9 : QuarticRefinedBCDEFG102L9810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L10 : QuarticRefinedBCDEFG102L10810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L12 : QuarticRefinedBCDEFG102L12810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG102L14 : QuarticRefinedBCDEFG102L14810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG108L0 : QuarticRefinedBCDEFG108L0810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG108L2 : QuarticRefinedBCDEFG108L2810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G
  | rBCDEFG108L5 : QuarticRefinedBCDEFG108L5810 A B C D E F G →
      QuarticChamberResidual6810 A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Honest leftover after every chamber kill of Files B/C.  Closed relative to `normalized810ScaleZero_quarticLoadLadderResidual`: the 1115-chamber exhaust, the tournament on the 11 carrier-refined cells, and every kill of modules 14, 19, 23, 29, 35 and 37.  Remaining: the all-constant corner and `QuarticChamberResidual6810` — 135 whole chambers and 37 refined leaves, i.e. the tower lane's open / deep-rescue / weak-band families, corner `H`, and the systems whose columns do not clear.  No `sorry`, no new axioms, no finite-root shortcut. -/
theorem normalized810ScaleZero_quarticChamber6Residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0 ∧
              B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
              E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0) ∨
            QuarticChamberResidual6810 A B C D E F G)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticLoadLadderResidual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · obtain ⟨hconeA, hexh, hlK, hbK, hdK, hzK, htK, hconst, hevenC, hevenE⟩ := hA
    refine Or.inl ⟨hconeA, ?_⟩
    by_cases hnc : B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0
    · rcases hconst with ⟨hl0, hb0, hd0, hz0⟩ | hn
      · exact Or.inl ⟨hl0, hb0, hd0, hz0, hnc.1, hnc.2.1, hnc.2.2.1,
          hnc.2.2.2.1, hnc.2.2.2.2.1, hnc.2.2.2.2.2⟩
      · exact absurd hnc hn
    · refine Or.inr ?_
      have hsupp := quarticChamberSupport810_of (j := j) (t := t)
        l beta gamma delta epsilon zeta eta theta A B C D E F G hconeA
        hjdiv hder
      cases hsupp with
      | size1 h =>
        cases h with
        | cB0 hc =>
          exact (quarticChamberB0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cC0 hc =>
          exact QuarticChamberResidual6810.rC0 hc
        | cD0 hc =>
          exact (quarticChamberD0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cE0 hc =>
          exact QuarticChamberResidual6810.rE0 hc
        | cF0 hc =>
          exact (quarticChamberF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cG0 hc =>
          exact QuarticChamberResidual6810.rG0 hc
      | size2 h =>
        cases h with
        | cBC0 hc =>
          exact (quarticChamberBC0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBC1 hc =>
          exact (quarticChamberBC1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBC2 hc =>
          exact (quarticChamberBC2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBD0 hc =>
          exact (quarticChamberBD0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBD1 hc =>
          exact (quarticChamberBD1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBD2 hc =>
          exact (quarticChamberBD2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBE0 hc =>
          exact (quarticChamberBE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBE1 hc =>
          exact (quarticChamberBE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBE2 hc =>
          exact (quarticChamberBE2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBF0 hc =>
          exact (quarticChamberBF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBF1 hc =>
          exact (quarticChamberBF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBF2 hc =>
          exact (quarticChamberBF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBF3 hc =>
          exact (quarticChamberBF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBF4 hc =>
          exact (quarticChamberBF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBG0 hc =>
          exact (quarticChamberBG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBG1 hc =>
          exact (quarticChamberBG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBG2 hc =>
          exact QuarticChamberResidual6810.rBG2 hc
        | cBG3 hc =>
          exact (quarticChamberBG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBG4 hc =>
          exact (quarticChamberBG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCD0 hc =>
          exact (quarticChamberCD0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCD1 hc =>
          exact (quarticChamberCD1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCD2 hc =>
          exact QuarticChamberResidual6810.rCD2 hc
        | cCE0 hc =>
          exact (quarticChamberCE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCE1 hc =>
          exact (quarticChamberCE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCE2 hc =>
          exact QuarticChamberResidual6810.rCE2 hc
        | cCF0 hc =>
          exact (quarticChamberCF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCF1 hc =>
          exact QuarticChamberResidual6810.rCF1 hc
        | cCF2 hc =>
          exact (quarticChamberCF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCF3 hc =>
          exact (quarticChamberCF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCF4 hc =>
          exact (quarticChamberCF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCG0 hc =>
          exact (quarticChamberCG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCG1 hc =>
          exact QuarticChamberResidual6810.rCG1 hc
        | cCG2 hc =>
          exact QuarticChamberResidual6810.rCG2 hc
        | cCG3 hc =>
          exact (quarticChamberCG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCG4 hc =>
          exact (quarticChamberCG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDE0 hc =>
          exact (quarticChamberDE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDE1 hc =>
          exact (quarticChamberDE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cDE2 hc =>
          exact (quarticChamberDE2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDF0 hc =>
          exact (quarticChamberDF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDF1 hc =>
          exact (quarticChamberDF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDF2 hc =>
          exact (quarticChamberDF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDG0 hc =>
          exact QuarticChamberResidual6810.rDG0 hc
        | cDG1 hc =>
          exact (quarticChamberDG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDG2 hc =>
          exact (quarticChamberDG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cEF0 hc =>
          exact QuarticChamberResidual6810.rEF0 hc
        | cEF1 hc =>
          exact (quarticChamberEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cEF2 hc =>
          exact (quarticChamberEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cEG0 hc =>
          exact QuarticChamberResidual6810.rEG0 hc
        | cEG1 hc =>
          exact (quarticChamberEG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cEG2 hc =>
          exact (quarticChamberEG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cFG0 hc =>
          exact QuarticChamberResidual6810.rFG0 hc
        | cFG1 hc =>
          exact QuarticChamberResidual6810.rFG1 hc
        | cFG2 hc =>
          exact (quarticChamberFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
      | size3 h =>
        cases h with
        | cBCD0 hc =>
          exact (quarticChamberBCD0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCD1 hc =>
          exact (quarticChamberBCD1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCD2 hc =>
          exact (quarticChamberBCD2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCD3 hc =>
          exact (quarticChamberBCD3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCD4 hc =>
          exact (quarticChamberBCD4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCD5 hc =>
          exact (quarticChamberBCD5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCD6 hc =>
          exact QuarticChamberResidual6810.rBCD6 hc
        | cBCE0 hc =>
          exact (quarticChamberBCE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCE1 hc =>
          exact (quarticChamberBCE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCE2 hc =>
          exact (quarticChamberBCE2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCE3 hc =>
          exact (quarticChamberBCE3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCE4 hc =>
          exact (quarticChamberBCE4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCE5 hc =>
          exact (quarticChamberBCE5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCE6 hc =>
          exact (quarticChamberBCE6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCF0 hc =>
          exact (quarticChamberBCF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCF1 hc =>
          exact (quarticChamberBCF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCF2 hc =>
          exact (quarticChamberBCF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF3 hc =>
          exact (quarticChamberBCF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF4 hc =>
          exact (quarticChamberBCF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF5 hc =>
          exact QuarticChamberResidual6810.rBCF5 hc
        | cBCF6 hc =>
          exact (quarticChamberBCF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF7 hc =>
          exact (quarticChamberBCF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF8 hc =>
          exact (quarticChamberBCF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF9 hc =>
          exact (quarticChamberBCF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCF10 hc =>
          exact (quarticChamberBCF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCF11 hc =>
          exact (quarticChamberBCF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCF12 hc =>
          exact (quarticChamberBCF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCG0 hc =>
          exact (quarticChamberBCG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCG1 hc =>
          exact (quarticChamberBCG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCG2 hc =>
          exact (quarticChamberBCG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCG3 hc =>
          exact QuarticChamberResidual6810.rBCG3 hc
        | cBCG4 hc =>
          exact (quarticChamberBCG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG5 hc =>
          exact QuarticChamberResidual6810.rBCG5 hc
        | cBCG6 hc =>
          exact (quarticChamberBCG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG7 hc =>
          exact (quarticChamberBCG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCG8 hc =>
          exact (quarticChamberBCG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG9 hc =>
          exact (quarticChamberBCG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG10 hc =>
          exact QuarticChamberResidual6810.rBCG10 hc
        | cBCG11 hc =>
          exact (quarticChamberBCG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCG12 hc =>
          exact (quarticChamberBCG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDE0 hc =>
          exact (quarticChamberBDE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDE1 hc =>
          exact (quarticChamberBDE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDE2 hc =>
          exact (quarticChamberBDE2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDE3 hc =>
          exact (quarticChamberBDE3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDE4 hc =>
          exact (quarticChamberBDE4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDE5 hc =>
          exact (quarticChamberBDE5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDE6 hc =>
          exact (quarticChamberBDE6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF0 hc =>
          exact (quarticChamberBDF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDF1 hc =>
          exact (quarticChamberBDF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF2 hc =>
          exact (quarticChamberBDF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF3 hc =>
          exact QuarticChamberResidual6810.rBDF3 hc
        | cBDF4 hc =>
          exact (quarticChamberBDF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDF5 hc =>
          exact (quarticChamberBDF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDF6 hc =>
          exact (quarticChamberBDF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF7 hc =>
          exact (quarticChamberBDF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF8 hc =>
          exact (quarticChamberBDF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDF9 hc =>
          exact (quarticChamberBDF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDF10 hc =>
          exact (quarticChamberBDF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDG0 hc =>
          exact (quarticChamberBDG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDG1 hc =>
          exact (quarticChamberBDG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDG2 hc =>
          exact QuarticChamberResidual6810.rBDG2 hc
        | cBDG3 hc =>
          exact (quarticChamberBDG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG4 hc =>
          exact (quarticChamberBDG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG5 hc =>
          exact (quarticChamberBDG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG6 hc =>
          exact (quarticChamberBDG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDG7 hc =>
          exact (quarticChamberBDG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG8 hc =>
          exact (quarticChamberBDG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG9 hc =>
          exact (quarticChamberBDG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDG10 hc =>
          exact (quarticChamberBDG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEF0 hc =>
          exact (quarticChamberBEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBEF1 hc =>
          exact (quarticChamberBEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF2 hc =>
          exact (quarticChamberBEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF3 hc =>
          exact QuarticChamberResidual6810.rBEF3 hc
        | cBEF4 hc =>
          exact (quarticChamberBEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBEF5 hc =>
          exact (quarticChamberBEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEF6 hc =>
          exact (quarticChamberBEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF7 hc =>
          exact (quarticChamberBEF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF8 hc =>
          exact (quarticChamberBEF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF9 hc =>
          exact (quarticChamberBEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEF10 hc =>
          exact (quarticChamberBEF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEG0 hc =>
          exact (quarticChamberBEG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBEG1 hc =>
          exact (quarticChamberBEG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBEG2 hc =>
          exact (quarticChamberBEG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBEG3 hc =>
          exact (quarticChamberBEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG4 hc =>
          exact (quarticChamberBEG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG5 hc =>
          exact (quarticChamberBEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG6 hc =>
          exact (quarticChamberBEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEG7 hc =>
          exact (quarticChamberBEG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG8 hc =>
          exact (quarticChamberBEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG9 hc =>
          exact (quarticChamberBEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEG10 hc =>
          exact (quarticChamberBEG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBFG0 hc =>
          exact (quarticChamberBFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBFG1 hc =>
          exact (quarticChamberBFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG2 hc =>
          exact (quarticChamberBFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG3 hc =>
          exact (quarticChamberBFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG4 hc =>
          exact (quarticChamberBFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG5 hc =>
          exact (quarticChamberBFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG6 hc =>
          exact (quarticChamberBFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBFG7 hc =>
          exact (quarticChamberBFG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBFG8 hc =>
          exact QuarticChamberResidual6810.rBFG8 hc
        | cBFG9 hc =>
          exact (quarticChamberBFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBFG10 hc =>
          exact (quarticChamberBFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBFG11 hc =>
          exact (quarticChamberBFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBFG12 hc =>
          exact (quarticChamberBFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDE0 hc =>
          exact (quarticChamberCDE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDE1 hc =>
          exact (quarticChamberCDE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDE2 hc =>
          exact QuarticChamberResidual6810.rCDE2 hc
        | cCDE3 hc =>
          exact (quarticChamberCDE3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDE4 hc =>
          exact (quarticChamberCDE4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDE5 hc =>
          exact (quarticChamberCDE5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDE6 hc =>
          exact QuarticChamberResidual6810.rCDE6 hc
        | cCDF0 hc =>
          exact (quarticChamberCDF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDF1 hc =>
          exact QuarticChamberResidual6810.rCDF1 hc
        | cCDF2 hc =>
          exact (quarticChamberCDF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDF3 hc =>
          exact (quarticChamberCDF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDF4 hc =>
          exact (quarticChamberCDF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDF5 hc =>
          exact (quarticChamberCDF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDF6 hc =>
          exact (quarticChamberCDF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDF7 hc =>
          exact (quarticChamberCDF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDF8 hc =>
          exact QuarticChamberResidual6810.rCDF8 hc
        | cCDF9 hc =>
          exact (quarticChamberCDF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDF10 hc =>
          exact (quarticChamberCDF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDG0 hc =>
          exact (quarticChamberCDG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDG1 hc =>
          exact QuarticChamberResidual6810.rCDG1 hc
        | cCDG2 hc =>
          exact QuarticChamberResidual6810.rCDG2 hc
        | cCDG3 hc =>
          exact QuarticChamberResidual6810.rCDG3 hc
        | cCDG4 hc =>
          exact QuarticChamberResidual6810.rCDG4 hc
        | cCDG5 hc =>
          exact (quarticChamberCDG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDG6 hc =>
          exact (quarticChamberCDG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDG7 hc =>
          exact (quarticChamberCDG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDG8 hc =>
          exact QuarticChamberResidual6810.rCDG8 hc
        | cCDG9 hc =>
          exact (quarticChamberCDG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDG10 hc =>
          exact (quarticChamberCDG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCEF0 hc =>
          exact (quarticChamberCEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF1 hc =>
          exact QuarticChamberResidual6810.rCEF1 hc
        | cCEF2 hc =>
          exact (quarticChamberCEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF3 hc =>
          exact (quarticChamberCEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF4 hc =>
          exact (quarticChamberCEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCEF5 hc =>
          exact (quarticChamberCEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF6 hc =>
          exact (quarticChamberCEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEF7 hc =>
          exact (quarticChamberCEF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF8 hc =>
          exact QuarticChamberResidual6810.rCEF8 hc
        | cCEF9 hc =>
          exact (quarticChamberCEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEF10 hc =>
          exact (quarticChamberCEF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEG0 hc =>
          exact (quarticChamberCEG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEG1 hc =>
          exact QuarticChamberResidual6810.rCEG1 hc
        | cCEG2 hc =>
          exact QuarticChamberResidual6810.rCEG2 hc
        | cCEG3 hc =>
          exact (quarticChamberCEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEG4 hc =>
          exact QuarticChamberResidual6810.rCEG4 hc
        | cCEG5 hc =>
          exact (quarticChamberCEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEG6 hc =>
          exact (quarticChamberCEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCEG7 hc =>
          exact (quarticChamberCEG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEG8 hc =>
          exact (quarticChamberCEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEG9 hc =>
          exact (quarticChamberCEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEG10 hc =>
          exact (quarticChamberCEG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCFG0 hc =>
          exact (quarticChamberCFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCFG1 hc =>
          exact QuarticChamberResidual6810.rCFG1 hc
        | cCFG2 hc =>
          exact (quarticChamberCFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCFG3 hc =>
          exact QuarticChamberResidual6810.rCFG3 hc
        | cCFG4 hc =>
          exact (quarticChamberCFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCFG5 hc =>
          exact (quarticChamberCFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCFG6 hc =>
          exact (quarticChamberCFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCFG7 hc =>
          exact QuarticChamberResidual6810.rCFG7 hc
        | cCFG8 hc =>
          exact QuarticChamberResidual6810.rCFG8 hc
        | cCFG9 hc =>
          exact (quarticChamberCFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCFG10 hc =>
          exact (quarticChamberCFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCFG11 hc =>
          exact (quarticChamberCFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCFG12 hc =>
          exact (quarticChamberCFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEF0 hc =>
          exact (quarticChamberDEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDEF1 hc =>
          exact (quarticChamberDEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEF2 hc =>
          exact QuarticChamberResidual6810.rDEF2 hc
        | cDEF3 hc =>
          exact (quarticChamberDEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEF4 hc =>
          exact (quarticChamberDEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDEF5 hc =>
          exact (quarticChamberDEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cDEF6 hc =>
          exact (quarticChamberDEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEG0 hc =>
          exact QuarticChamberResidual6810.rDEG0 hc
        | cDEG1 hc =>
          exact (quarticChamberDEG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEG2 hc =>
          exact (quarticChamberDEG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cDEG3 hc =>
          exact (quarticChamberDEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEG4 hc =>
          exact QuarticChamberResidual6810.rDEG4 hc
        | cDEG5 hc =>
          exact (quarticChamberDEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEG6 hc =>
          exact (quarticChamberDEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDFG0 hc =>
          exact QuarticChamberResidual6810.rDFG0 hc
        | cDFG1 hc =>
          exact QuarticChamberResidual6810.rDFG1 hc
        | cDFG2 hc =>
          exact (quarticChamberDFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDFG3 hc =>
          exact (quarticChamberDFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDFG4 hc =>
          exact (quarticChamberDFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDFG5 hc =>
          exact (quarticChamberDFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDFG6 hc =>
          exact (quarticChamberDFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cEFG0 hc =>
          exact QuarticChamberResidual6810.rEFG0 hc
        | cEFG1 hc =>
          exact QuarticChamberResidual6810.rEFG1 hc
        | cEFG2 hc =>
          exact (quarticChamberEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cEFG3 hc =>
          exact (quarticChamberEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cEFG4 hc =>
          exact (quarticChamberEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cEFG5 hc =>
          exact (quarticChamberEFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cEFG6 hc =>
          exact (quarticChamberEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
      | size4 h =>
        cases h with
        | cBCDE0 hc =>
          exact (quarticChamberBCDE0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDE1 hc =>
          exact (quarticChamberBCDE1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCDE2 hc =>
          exact (quarticChamberBCDE2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDE3 hc =>
          exact (quarticChamberBCDE3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDE4 hc =>
          exact (quarticChamberBCDE4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDE5 hc =>
          exact (quarticChamberBCDE5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDE6 hc =>
          exact (quarticChamberBCDE6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDE7 hc =>
          exact (quarticChamberBCDE7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDE8 hc =>
          exact (quarticChamberBCDE8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDE9 hc =>
          exact (quarticChamberBCDE9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDE10 hc =>
          exact (quarticChamberBCDE10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDE11 hc =>
          exact (quarticChamberBCDE11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDE12 hc =>
          exact (quarticChamberBCDE12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDE13 hc =>
          exact (quarticChamberBCDE13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCDE14 hc =>
          exact (quarticChamberBCDE14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDF0 hc =>
          exact (quarticChamberBCDF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDF1 hc =>
          exact (quarticChamberBCDF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCDF2 hc =>
          exact (quarticChamberBCDF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF3 hc =>
          exact (quarticChamberBCDF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF4 hc =>
          exact (quarticChamberBCDF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF5 hc =>
          exact (quarticChamberBCDF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDF6 hc =>
          exact (quarticChamberBCDF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDF7 hc =>
          exact (quarticChamberBCDF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDF8 hc =>
          exact (quarticChamberBCDF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDF9 hc =>
          exact (quarticChamberBCDF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF10 hc =>
          exact (quarticChamberBCDF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDF11 hc =>
          exact (quarticChamberBCDF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDF12 hc =>
          exact (quarticChamberBCDF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDF13 hc =>
          exact (quarticChamberBCDF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF14 hc =>
          exact (quarticChamberBCDF14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF15 hc =>
          exact (quarticChamberBCDF15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDF16 hc =>
          exact (quarticChamberBCDF16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF17 hc =>
          exact (quarticChamberBCDF17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF18 hc =>
          exact (quarticChamberBCDF18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDF19 hc =>
          exact (quarticChamberBCDF19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDF20 hc =>
          exact (quarticChamberBCDF20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDF21 hc =>
          exact (quarticChamberBCDF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF22 hc =>
          exact (quarticChamberBCDF22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDF23 hc =>
          exact (quarticChamberBCDF23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDF24 hc =>
          exact (quarticChamberBCDF24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDF25 hc =>
          exact (quarticChamberBCDF25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDF26 hc =>
          exact (quarticChamberBCDF26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDG0 hc =>
          exact (quarticChamberBCDG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDG1 hc =>
          exact (quarticChamberBCDG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCDG2 hc =>
          exact (quarticChamberBCDG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDG3 hc =>
          exact (quarticChamberBCDG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBCDG4 hc =>
          exact (quarticChamberBCDG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG5 hc =>
          exact (quarticChamberBCDG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDG6 hc =>
          exact (quarticChamberBCDG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDG7 hc =>
          exact (quarticChamberBCDG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDG8 hc =>
          exact (quarticChamberBCDG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDG9 hc =>
          exact (quarticChamberBCDG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG10 hc =>
          exact (quarticChamberBCDG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG11 hc =>
          exact (quarticChamberBCDG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG12 hc =>
          exact (quarticChamberBCDG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG13 hc =>
          exact (quarticChamberBCDG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDG14 hc =>
          exact (quarticChamberBCDG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG15 hc =>
          exact (quarticChamberBCDG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG16 hc =>
          exact QuarticChamberResidual6810.rBCDG16 hc
        | cBCDG17 hc =>
          exact QuarticChamberResidual6810.rBCDG17 hc
        | cBCDG18 hc =>
          exact QuarticChamberResidual6810.rBCDG18 hc
        | cBCDG19 hc =>
          exact (quarticChamberBCDG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDG20 hc =>
          exact (quarticChamberBCDG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG21 hc =>
          exact (quarticChamberBCDG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG22 hc =>
          exact (quarticChamberBCDG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG23 hc =>
          exact (quarticChamberBCDG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDG24 hc =>
          exact QuarticChamberResidual6810.rBCDG24 hc
        | cBCDG25 hc =>
          exact (quarticChamberBCDG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDG26 hc =>
          exact (quarticChamberBCDG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEF0 hc =>
          exact (quarticChamberBCEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEF1 hc =>
          exact (quarticChamberBCEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCEF2 hc =>
          exact (quarticChamberBCEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF3 hc =>
          exact (quarticChamberBCEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF4 hc =>
          exact (quarticChamberBCEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF5 hc =>
          exact (quarticChamberBCEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCEF6 hc =>
          exact (quarticChamberBCEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEF7 hc =>
          exact (quarticChamberBCEF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg).elim
        | cBCEF8 hc =>
          exact (quarticChamberBCEF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEF9 hc =>
          exact (quarticChamberBCEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF10 hc =>
          exact (quarticChamberBCEF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEF11 hc =>
          exact (quarticChamberBCEF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEF12 hc =>
          exact (quarticChamberBCEF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEF13 hc =>
          exact (quarticChamberBCEF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF14 hc =>
          exact (quarticChamberBCEF14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF15 hc =>
          exact (quarticChamberBCEF15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEF16 hc =>
          exact (quarticChamberBCEF16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF17 hc =>
          exact (quarticChamberBCEF17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF18 hc =>
          exact (quarticChamberBCEF18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEF19 hc =>
          exact (quarticChamberBCEF19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF20 hc =>
          exact (quarticChamberBCEF20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEF21 hc =>
          exact (quarticChamberBCEF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF22 hc =>
          exact (quarticChamberBCEF22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF23 hc =>
          exact (quarticChamberBCEF23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCEF24 hc =>
          exact (quarticChamberBCEF24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEF25 hc =>
          exact (quarticChamberBCEF25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEF26 hc =>
          exact (quarticChamberBCEF26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEG0 hc =>
          exact (quarticChamberBCEG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEG1 hc =>
          exact (quarticChamberBCEG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCEG2 hc =>
          exact (quarticChamberBCEG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEG3 hc =>
          exact (quarticChamberBCEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBCEG4 hc =>
          exact (quarticChamberBCEG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG5 hc =>
          exact (quarticChamberBCEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCEG6 hc =>
          exact (quarticChamberBCEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEG7 hc =>
          exact (quarticChamberBCEG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCEG8 hc =>
          exact (quarticChamberBCEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEG9 hc =>
          exact (quarticChamberBCEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG10 hc =>
          exact (quarticChamberBCEG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG11 hc =>
          exact (quarticChamberBCEG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG12 hc =>
          exact (quarticChamberBCEG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG13 hc =>
          exact (quarticChamberBCEG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEG14 hc =>
          exact (quarticChamberBCEG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG15 hc =>
          exact (quarticChamberBCEG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG16 hc =>
          exact (quarticChamberBCEG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCEG17 hc =>
          exact (quarticChamberBCEG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEG18 hc =>
          exact (quarticChamberBCEG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCEG19 hc =>
          exact (quarticChamberBCEG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEG20 hc =>
          exact (quarticChamberBCEG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG21 hc =>
          exact (quarticChamberBCEG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG22 hc =>
          exact (quarticChamberBCEG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG23 hc =>
          exact (quarticChamberBCEG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCEG24 hc =>
          exact (quarticChamberBCEG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEG25 hc =>
          exact (quarticChamberBCEG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEG26 hc =>
          exact (quarticChamberBCEG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCFG0 hc =>
          exact (quarticChamberBCFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCFG1 hc =>
          exact (quarticChamberBCFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCFG2 hc =>
          exact (quarticChamberBCFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG3 hc =>
          exact (quarticChamberBCFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG4 hc =>
          exact (quarticChamberBCFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG5 hc =>
          exact (quarticChamberBCFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG6 hc =>
          exact (quarticChamberBCFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG7 hc =>
          exact QuarticChamberResidual6810.rBCFG7 hc
        | cBCFG8 hc =>
          exact (quarticChamberBCFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG9 hc =>
          exact (quarticChamberBCFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG10 hc =>
          exact (quarticChamberBCFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG11 hc =>
          exact QuarticChamberResidual6810.rBCFG11 hc
        | cBCFG12 hc =>
          exact (quarticChamberBCFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG13 hc =>
          exact (quarticChamberBCFG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG14 hc =>
          exact (quarticChamberBCFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCFG15 hc =>
          exact QuarticChamberResidual6810.rBCFG15 hc
        | cBCFG16 hc =>
          exact (quarticChamberBCFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG17 hc =>
          exact QuarticChamberResidual6810.rBCFG17 hc
        | cBCFG18 hc =>
          exact (quarticChamberBCFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG19 hc =>
          exact (quarticChamberBCFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCFG20 hc =>
          exact (quarticChamberBCFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG21 hc =>
          exact (quarticChamberBCFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCFG22 hc =>
          exact (quarticChamberBCFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG23 hc =>
          exact (quarticChamberBCFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG24 hc =>
          exact (quarticChamberBCFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCFG25 hc =>
          exact (quarticChamberBCFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG26 hc =>
          exact (quarticChamberBCFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG27 hc =>
          exact (quarticChamberBCFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG28 hc =>
          exact (quarticChamberBCFG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCFG29 hc =>
          exact (quarticChamberBCFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCFG30 hc =>
          exact (quarticChamberBCFG30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG31 hc =>
          exact (quarticChamberBCFG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCFG32 hc =>
          exact (quarticChamberBCFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF0 hc =>
          exact (quarticChamberBDEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEF1 hc =>
          exact (quarticChamberBDEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF2 hc =>
          exact (quarticChamberBDEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF3 hc =>
          exact (quarticChamberBDEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEF4 hc =>
          exact (quarticChamberBDEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEF5 hc =>
          exact (quarticChamberBDEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF6 hc =>
          exact (quarticChamberBDEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEF7 hc =>
          exact (quarticChamberBDEF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBDEF8 hc =>
          exact (quarticChamberBDEF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF9 hc =>
          exact (quarticChamberBDEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF10 hc =>
          exact (quarticChamberBDEF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEF11 hc =>
          exact (quarticChamberBDEF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEF12 hc =>
          exact (quarticChamberBDEF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF13 hc =>
          exact (quarticChamberBDEF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF14 hc =>
          exact (quarticChamberBDEF14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF15 hc =>
          exact (quarticChamberBDEF15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF16 hc =>
          exact (quarticChamberBDEF16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEF17 hc =>
          exact (quarticChamberBDEF17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEF18 hc =>
          exact (quarticChamberBDEF18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEF19 hc =>
          exact (quarticChamberBDEF19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF20 hc =>
          exact (quarticChamberBDEF20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF21 hc =>
          exact (quarticChamberBDEF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEF22 hc =>
          exact (quarticChamberBDEF22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG0 hc =>
          exact (quarticChamberBDEG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEG1 hc =>
          exact (quarticChamberBDEG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEG2 hc =>
          exact (quarticChamberBDEG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBDEG3 hc =>
          exact (quarticChamberBDEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG4 hc =>
          exact (quarticChamberBDEG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG5 hc =>
          exact (quarticChamberBDEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG6 hc =>
          exact (quarticChamberBDEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG7 hc =>
          exact (quarticChamberBDEG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg hpiDeg).elim
        | cBDEG8 hc =>
          exact (quarticChamberBDEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG9 hc =>
          exact (quarticChamberBDEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG10 hc =>
          exact (quarticChamberBDEG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG11 hc =>
          exact (quarticChamberBDEG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG12 hc =>
          exact (quarticChamberBDEG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEG13 hc =>
          exact (quarticChamberBDEG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG14 hc =>
          exact (quarticChamberBDEG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG15 hc =>
          exact (quarticChamberBDEG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG16 hc =>
          exact (quarticChamberBDEG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEG17 hc =>
          exact (quarticChamberBDEG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEG18 hc =>
          exact (quarticChamberBDEG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG19 hc =>
          exact (quarticChamberBDEG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG20 hc =>
          exact (quarticChamberBDEG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG21 hc =>
          exact (quarticChamberBDEG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEG22 hc =>
          exact (quarticChamberBDEG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDFG0 hc =>
          exact (quarticChamberBDFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDFG1 hc =>
          exact (quarticChamberBDFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG2 hc =>
          exact (quarticChamberBDFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG3 hc =>
          exact (quarticChamberBDFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG4 hc =>
          exact (quarticChamberBDFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG5 hc =>
          exact (quarticChamberBDFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDFG6 hc =>
          exact (quarticChamberBDFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDFG7 hc =>
          exact QuarticChamberResidual6810.rBDFG7 hc
        | cBDFG8 hc =>
          exact (quarticChamberBDFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG9 hc =>
          exact (quarticChamberBDFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDFG10 hc =>
          exact (quarticChamberBDFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDFG11 hc =>
          exact (quarticChamberBDFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDFG12 hc =>
          exact (quarticChamberBDFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG13 hc =>
          exact (quarticChamberBDFG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDFG14 hc =>
          exact (quarticChamberBDFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBDFG15 hc =>
          exact (quarticChamberBDFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG16 hc =>
          exact (quarticChamberBDFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG17 hc =>
          exact (quarticChamberBDFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG18 hc =>
          exact (quarticChamberBDFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDFG19 hc =>
          exact (quarticChamberBDFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG20 hc =>
          exact (quarticChamberBDFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG21 hc =>
          exact (quarticChamberBDFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDFG22 hc =>
          exact (quarticChamberBDFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDFG23 hc =>
          exact (quarticChamberBDFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDFG24 hc =>
          exact (quarticChamberBDFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDFG25 hc =>
          exact (quarticChamberBDFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDFG26 hc =>
          exact (quarticChamberBDFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEFG0 hc =>
          exact (quarticChamberBEFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBEFG1 hc =>
          exact (quarticChamberBEFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG2 hc =>
          exact (quarticChamberBEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG3 hc =>
          exact (quarticChamberBEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG4 hc =>
          exact (quarticChamberBEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG5 hc =>
          exact (quarticChamberBEFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBEFG6 hc =>
          exact (quarticChamberBEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBEFG7 hc =>
          exact QuarticChamberResidual6810.rBEFG7 hc
        | cBEFG8 hc =>
          exact (quarticChamberBEFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG9 hc =>
          exact (quarticChamberBEFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEFG10 hc =>
          exact (quarticChamberBEFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBEFG11 hc =>
          exact (quarticChamberBEFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEFG12 hc =>
          exact (quarticChamberBEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG13 hc =>
          exact (quarticChamberBEFG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBEFG14 hc =>
          exact (quarticChamberBEFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBEFG15 hc =>
          exact (quarticChamberBEFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG16 hc =>
          exact (quarticChamberBEFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG17 hc =>
          exact (quarticChamberBEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG18 hc =>
          exact (quarticChamberBEFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBEFG19 hc =>
          exact (quarticChamberBEFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG20 hc =>
          exact (quarticChamberBEFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG21 hc =>
          exact (quarticChamberBEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG22 hc =>
          exact (quarticChamberBEFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG23 hc =>
          exact (quarticChamberBEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBEFG24 hc =>
          exact (quarticChamberBEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEFG25 hc =>
          exact (quarticChamberBEFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBEFG26 hc =>
          exact (quarticChamberBEFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEF0 hc =>
          exact (quarticChamberCDEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF1 hc =>
          exact QuarticChamberResidual6810.rCDEF1 hc
        | cCDEF2 hc =>
          exact (quarticChamberCDEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF3 hc =>
          exact (quarticChamberCDEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF4 hc =>
          exact (quarticChamberCDEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEF5 hc =>
          exact (quarticChamberCDEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEF6 hc =>
          exact (quarticChamberCDEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEF7 hc =>
          exact (quarticChamberCDEF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cCDEF8 hc =>
          exact (quarticChamberCDEF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEF9 hc =>
          exact (quarticChamberCDEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF10 hc =>
          exact (quarticChamberCDEF10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEF11 hc =>
          exact (quarticChamberCDEF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF12 hc =>
          exact (quarticChamberCDEF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEF13 hc =>
          exact (quarticChamberCDEF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF14 hc =>
          exact (quarticChamberCDEF14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cCDEF15 hc =>
          exact (quarticChamberCDEF15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEF16 hc =>
          exact (quarticChamberCDEF16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEF17 hc =>
          exact (quarticChamberCDEF17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEF18 hc =>
          exact (quarticChamberCDEF18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEF19 hc =>
          exact (quarticChamberCDEF19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF20 hc =>
          exact (quarticChamberCDEF20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEF21 hc =>
          exact (quarticChamberCDEF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEF22 hc =>
          exact (quarticChamberCDEF22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEG0 hc =>
          exact (quarticChamberCDEG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG1 hc =>
          exact QuarticChamberResidual6810.rCDEG1 hc
        | cCDEG2 hc =>
          exact QuarticChamberResidual6810.rCDEG2 hc
        | cCDEG3 hc =>
          exact QuarticChamberResidual6810.rCDEG3 hc
        | cCDEG4 hc =>
          exact QuarticChamberResidual6810.rCDEG4 hc
        | cCDEG5 hc =>
          exact (quarticChamberCDEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEG6 hc =>
          exact (quarticChamberCDEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEG7 hc =>
          exact (quarticChamberCDEG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEG8 hc =>
          exact (quarticChamberCDEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEG9 hc =>
          exact QuarticChamberResidual6810.rCDEG9 hc
        | cCDEG10 hc =>
          exact QuarticChamberResidual6810.rCDEG10 hc
        | cCDEG11 hc =>
          exact (quarticChamberCDEG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEG12 hc =>
          exact (quarticChamberCDEG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEG13 hc =>
          exact (quarticChamberCDEG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG14 hc =>
          exact QuarticChamberResidual6810.rCDEG14 hc
        | cCDEG15 hc =>
          exact (quarticChamberCDEG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEG16 hc =>
          exact (quarticChamberCDEG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEG17 hc =>
          exact (quarticChamberCDEG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEG18 hc =>
          exact (quarticChamberCDEG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG19 hc =>
          exact (quarticChamberCDEG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG20 hc =>
          exact QuarticChamberResidual6810.rCDEG20 hc
        | cCDEG21 hc =>
          exact (quarticChamberCDEG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEG22 hc =>
          exact (quarticChamberCDEG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDFG0 hc =>
          exact (quarticChamberCDFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG1 hc =>
          exact QuarticChamberResidual6810.rCDFG1 hc
        | cCDFG2 hc =>
          exact (quarticChamberCDFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG3 hc =>
          exact QuarticChamberResidual6810.rCDFG3 hc
        | cCDFG4 hc =>
          exact (quarticChamberCDFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDFG5 hc =>
          exact QuarticChamberResidual6810.rCDFG5 hc
        | cCDFG6 hc =>
          exact (quarticChamberCDFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDFG7 hc =>
          exact QuarticChamberResidual6810.rCDFG7 hc
        | cCDFG8 hc =>
          exact (quarticChamberCDFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDFG9 hc =>
          exact (quarticChamberCDFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG10 hc =>
          exact (quarticChamberCDFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDFG11 hc =>
          exact (quarticChamberCDFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDFG12 hc =>
          exact (quarticChamberCDFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDFG13 hc =>
          exact QuarticChamberResidual6810.rCDFG13 hc
        | cCDFG14 hc =>
          exact QuarticChamberResidual6810.rCDFG14 hc
        | cCDFG15 hc =>
          exact QuarticChamberResidual6810.rCDFG15 hc
        | cCDFG16 hc =>
          exact QuarticChamberResidual6810.rCDFG16 hc
        | cCDFG17 hc =>
          exact (quarticChamberCDFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDFG18 hc =>
          exact (quarticChamberCDFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDFG19 hc =>
          exact (quarticChamberCDFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG20 hc =>
          exact QuarticChamberResidual6810.rCDFG20 hc
        | cCDFG21 hc =>
          exact (quarticChamberCDFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hxiDeg).elim
        | cCDFG22 hc =>
          exact (quarticChamberCDFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDFG23 hc =>
          exact (quarticChamberCDFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDFG24 hc =>
          exact (quarticChamberCDFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDFG25 hc =>
          exact (quarticChamberCDFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDFG26 hc =>
          exact (quarticChamberCDFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCEFG0 hc =>
          exact (quarticChamberCEFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG1 hc =>
          exact QuarticChamberResidual6810.rCEFG1 hc
        | cCEFG2 hc =>
          exact (quarticChamberCEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG3 hc =>
          exact QuarticChamberResidual6810.rCEFG3 hc
        | cCEFG4 hc =>
          exact (quarticChamberCEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCEFG5 hc =>
          exact QuarticChamberResidual6810.rCEFG5 hc
        | cCEFG6 hc =>
          exact (quarticChamberCEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCEFG7 hc =>
          exact QuarticChamberResidual6810.rCEFG7 hc
        | cCEFG8 hc =>
          exact (quarticChamberCEFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG9 hc =>
          exact (quarticChamberCEFG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG10 hc =>
          exact (quarticChamberCEFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCEFG11 hc =>
          exact (quarticChamberCEFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG12 hc =>
          exact (quarticChamberCEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG13 hc =>
          exact QuarticChamberResidual6810.rCEFG13 hc
        | cCEFG14 hc =>
          exact QuarticChamberResidual6810.rCEFG14 hc
        | cCEFG15 hc =>
          exact QuarticChamberResidual6810.rCEFG15 hc
        | cCEFG16 hc =>
          exact QuarticChamberResidual6810.rCEFG16 hc
        | cCEFG17 hc =>
          exact (quarticChamberCEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG18 hc =>
          exact (quarticChamberCEFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCEFG19 hc =>
          exact (quarticChamberCEFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG20 hc =>
          exact QuarticChamberResidual6810.rCEFG20 hc
        | cCEFG21 hc =>
          exact (quarticChamberCEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG22 hc =>
          exact (quarticChamberCEFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG23 hc =>
          exact (quarticChamberCEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCEFG24 hc =>
          exact (quarticChamberCEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG25 hc =>
          exact (quarticChamberCEFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCEFG26 hc =>
          exact (quarticChamberCEFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEFG0 hc =>
          exact QuarticChamberResidual6810.rDEFG0 hc
        | cDEFG1 hc =>
          exact QuarticChamberResidual6810.rDEFG1 hc
        | cDEFG2 hc =>
          exact (quarticChamberDEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEFG3 hc =>
          exact (quarticChamberDEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEFG4 hc =>
          exact QuarticChamberResidual6810.rDEFG4 hc
        | cDEFG5 hc =>
          exact QuarticChamberResidual6810.rDEFG5 hc
        | cDEFG6 hc =>
          exact (quarticChamberDEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEFG7 hc =>
          exact (quarticChamberDEFG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cDEFG8 hc =>
          exact QuarticChamberResidual6810.rDEFG8 hc
        | cDEFG9 hc =>
          exact QuarticChamberResidual6810.rDEFG9 hc
        | cDEFG10 hc =>
          exact (quarticChamberDEFG10810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEFG11 hc =>
          exact (quarticChamberDEFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEFG12 hc =>
          exact (quarticChamberDEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEFG13 hc =>
          exact (quarticChamberDEFG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cDEFG14 hc =>
          exact (quarticChamberDEFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
      | size5 h =>
        cases h with
        | cBCDEF0 hc =>
          exact (quarticChamberBCDEF0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF1 hc =>
          exact (quarticChamberBCDEF1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCDEF2 hc =>
          exact (quarticChamberBCDEF2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF3 hc =>
          exact (quarticChamberBCDEF3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF4 hc =>
          exact (quarticChamberBCDEF4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF5 hc =>
          exact (quarticChamberBCDEF5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDEF6 hc =>
          exact (quarticChamberBCDEF6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF7 hc =>
          exact (quarticChamberBCDEF7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEF8 hc =>
          exact (quarticChamberBCDEF8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF9 hc =>
          exact (quarticChamberBCDEF9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF10 hc =>
          exact QuarticChamberResidual6810.rBCDEF10 hc
        | cBCDEF11 hc =>
          exact (quarticChamberBCDEF11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF12 hc =>
          exact (quarticChamberBCDEF12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF13 hc =>
          exact (quarticChamberBCDEF13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg).elim
        | cBCDEF14 hc =>
          exact (quarticChamberBCDEF14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF15 hc =>
          exact (quarticChamberBCDEF15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF16 hc =>
          exact (quarticChamberBCDEF16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF17 hc =>
          exact (quarticChamberBCDEF17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF18 hc =>
          exact (quarticChamberBCDEF18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF19 hc =>
          exact (quarticChamberBCDEF19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF20 hc =>
          exact (quarticChamberBCDEF20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEF21 hc =>
          exact (quarticChamberBCDEF21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF22 hc =>
          exact (quarticChamberBCDEF22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF23 hc =>
          exact (quarticChamberBCDEF23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF24 hc =>
          exact (quarticChamberBCDEF24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF25 hc =>
          exact (quarticChamberBCDEF25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF26 hc =>
          exact (quarticChamberBCDEF26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF27 hc =>
          exact (quarticChamberBCDEF27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF28 hc =>
          exact (quarticChamberBCDEF28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF29 hc =>
          exact (quarticChamberBCDEF29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF30 hc =>
          exact (quarticChamberBCDEF30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF31 hc =>
          exact (quarticChamberBCDEF31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF32 hc =>
          exact (quarticChamberBCDEF32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF33 hc =>
          exact (quarticChamberBCDEF33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEF34 hc =>
          exact (quarticChamberBCDEF34810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF35 hc =>
          exact (quarticChamberBCDEF35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF36 hc =>
          exact (quarticChamberBCDEF36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF37 hc =>
          exact (quarticChamberBCDEF37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF38 hc =>
          exact (quarticChamberBCDEF38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF39 hc =>
          exact (quarticChamberBCDEF39810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF40 hc =>
          exact (quarticChamberBCDEF40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF41 hc =>
          exact (quarticChamberBCDEF41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF42 hc =>
          exact (quarticChamberBCDEF42810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDEF43 hc =>
          exact (quarticChamberBCDEF43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF44 hc =>
          exact (quarticChamberBCDEF44810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF45 hc =>
          exact (quarticChamberBCDEF45810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF46 hc =>
          exact (quarticChamberBCDEF46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEF47 hc =>
          exact (quarticChamberBCDEF47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEF48 hc =>
          exact (quarticChamberBCDEF48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEF49 hc =>
          exact (quarticChamberBCDEF49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF50 hc =>
          exact (quarticChamberBCDEF50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF51 hc =>
          exact (quarticChamberBCDEF51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCDEF52 hc =>
          exact (quarticChamberBCDEF52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEF53 hc =>
          exact (quarticChamberBCDEF53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEF54 hc =>
          exact (quarticChamberBCDEF54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG0 hc =>
          exact (quarticChamberBCDEG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEG1 hc =>
          exact (quarticChamberBCDEG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCDEG2 hc =>
          exact (quarticChamberBCDEG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEG3 hc =>
          exact (quarticChamberBCDEG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBCDEG4 hc =>
          exact (quarticChamberBCDEG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG5 hc =>
          exact (quarticChamberBCDEG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDEG6 hc =>
          exact (quarticChamberBCDEG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEG7 hc =>
          exact (quarticChamberBCDEG7810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG8 hc =>
          exact (quarticChamberBCDEG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG9 hc =>
          exact (quarticChamberBCDEG9810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG10 hc =>
          exact QuarticChamberResidual6810.rBCDEG10 hc
        | cBCDEG11 hc =>
          exact (quarticChamberBCDEG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEG12 hc =>
          exact (quarticChamberBCDEG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEG13 hc =>
          exact (quarticChamberBCDEG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCDEG14 hc =>
          exact (quarticChamberBCDEG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG15 hc =>
          exact (quarticChamberBCDEG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG16 hc =>
          exact (quarticChamberBCDEG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG17 hc =>
          exact (quarticChamberBCDEG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG18 hc =>
          exact (quarticChamberBCDEG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG19 hc =>
          exact (quarticChamberBCDEG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG20 hc =>
          exact (quarticChamberBCDEG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg hpiDeg).elim
        | cBCDEG21 hc =>
          exact (quarticChamberBCDEG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG22 hc =>
          exact (quarticChamberBCDEG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG23 hc =>
          exact (quarticChamberBCDEG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG24 hc =>
          exact (quarticChamberBCDEG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG25 hc =>
          exact (quarticChamberBCDEG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEG26 hc =>
          exact (quarticChamberBCDEG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG27 hc =>
          exact (quarticChamberBCDEG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG28 hc =>
          exact (quarticChamberBCDEG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDEG29 hc =>
          exact (quarticChamberBCDEG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEG30 hc =>
          rcases quarticChamberBCDEG30810_refine A B C D E F G hc with
            h0 | h1 | h2 | h3 | h4
          · exact QuarticChamberResidual6810.rBCDEG30L0 h0
          · exact (quarticRefinedBCDEG30L1810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h1 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCDEG30L2 h2
          · exact QuarticChamberResidual6810.rBCDEG30L3 h3
          · exact QuarticChamberResidual6810.rBCDEG30L4 h4
        | cBCDEG31 hc =>
          exact (quarticChamberBCDEG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG32 hc =>
          exact (quarticChamberBCDEG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEG33 hc =>
          exact (quarticChamberBCDEG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEG34 hc =>
          exact (quarticChamberBCDEG34810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEG35 hc =>
          exact (quarticChamberBCDEG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG36 hc =>
          rcases quarticChamberBCDEG36810_refine A B C D E F G hc with
            h0 | h1 | h2
          · exact QuarticChamberResidual6810.rBCDEG36L0 h0
          · exact (quarticRefinedBCDEG36L1810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h1 hnc hkapDeg hnuDeg hxiDeg).elim
          · exact (quarticRefinedBCDEG36L2810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h2 hnc hkapDeg hnuDeg).elim
        | cBCDEG37 hc =>
          exact (quarticChamberBCDEG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG38 hc =>
          exact (quarticChamberBCDEG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG39 hc =>
          exact (quarticChamberBCDEG39810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG40 hc =>
          exact (quarticChamberBCDEG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG41 hc =>
          exact (quarticChamberBCDEG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG42 hc =>
          exact (quarticChamberBCDEG42810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDEG43 hc =>
          exact (quarticChamberBCDEG43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG44 hc =>
          exact (quarticChamberBCDEG44810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEG45 hc =>
          exact (quarticChamberBCDEG45810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG46 hc =>
          exact (quarticChamberBCDEG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEG47 hc =>
          exact (quarticChamberBCDEG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEG48 hc =>
          exact (quarticChamberBCDEG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG49 hc =>
          exact (quarticChamberBCDEG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG50 hc =>
          exact (quarticChamberBCDEG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG51 hc =>
          exact (quarticChamberBCDEG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCDEG52 hc =>
          exact (quarticChamberBCDEG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEG53 hc =>
          exact (quarticChamberBCDEG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEG54 hc =>
          exact (quarticChamberBCDEG54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG0 hc =>
          exact (quarticChamberBCDFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG1 hc =>
          exact (quarticChamberBCDFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCDFG2 hc =>
          exact (quarticChamberBCDFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG3 hc =>
          exact (quarticChamberBCDFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG4 hc =>
          exact (quarticChamberBCDFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG5 hc =>
          exact (quarticChamberBCDFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG6 hc =>
          exact (quarticChamberBCDFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDFG7 hc =>
          rcases quarticChamberBCDFG7810_refine A B C D E F G hc with
            h0 | h1 | h2
          · exact (quarticRefinedBCDFG7L0810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h0 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCDFG7L1 h1
          · exact QuarticChamberResidual6810.rBCDFG7L2 h2
        | cBCDFG8 hc =>
          exact (quarticChamberBCDFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG9 hc =>
          exact QuarticChamberResidual6810.rBCDFG9 hc
        | cBCDFG10 hc =>
          exact QuarticChamberResidual6810.rBCDFG10 hc
        | cBCDFG11 hc =>
          exact (quarticChamberBCDFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG12 hc =>
          exact (quarticChamberBCDFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG13 hc =>
          exact (quarticChamberBCDFG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG14 hc =>
          exact QuarticChamberResidual6810.rBCDFG14 hc
        | cBCDFG15 hc =>
          exact (quarticChamberBCDFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG16 hc =>
          exact (quarticChamberBCDFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG17 hc =>
          exact (quarticChamberBCDFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDFG18 hc =>
          exact (quarticChamberBCDFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG19 hc =>
          exact (quarticChamberBCDFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDFG20 hc =>
          exact (quarticChamberBCDFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG21 hc =>
          exact (quarticChamberBCDFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG22 hc =>
          exact (quarticChamberBCDFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG23 hc =>
          exact (quarticChamberBCDFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG24 hc =>
          exact (quarticChamberBCDFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG25 hc =>
          exact (quarticChamberBCDFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG26 hc =>
          exact (quarticChamberBCDFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG27 hc =>
          exact (quarticChamberBCDFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBCDFG28 hc =>
          exact (quarticChamberBCDFG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG29 hc =>
          exact (quarticChamberBCDFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDFG30 hc =>
          exact (quarticChamberBCDFG30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG31 hc =>
          exact (quarticChamberBCDFG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG32 hc =>
          exact (quarticChamberBCDFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG33 hc =>
          exact (quarticChamberBCDFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG34 hc =>
          exact (quarticChamberBCDFG34810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG35 hc =>
          exact (quarticChamberBCDFG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG36 hc =>
          exact (quarticChamberBCDFG36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG37 hc =>
          exact (quarticChamberBCDFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG38 hc =>
          exact (quarticChamberBCDFG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG39 hc =>
          exact (quarticChamberBCDFG39810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG40 hc =>
          exact (quarticChamberBCDFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG41 hc =>
          exact (quarticChamberBCDFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG42 hc =>
          exact (quarticChamberBCDFG42810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG43 hc =>
          exact (quarticChamberBCDFG43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG44 hc =>
          exact (quarticChamberBCDFG44810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG45 hc =>
          exact QuarticChamberResidual6810.rBCDFG45 hc
        | cBCDFG46 hc =>
          exact (quarticChamberBCDFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG47 hc =>
          exact (quarticChamberBCDFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG48 hc =>
          exact (quarticChamberBCDFG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG49 hc =>
          exact (quarticChamberBCDFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG50 hc =>
          exact (quarticChamberBCDFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG51 hc =>
          exact (quarticChamberBCDFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG52 hc =>
          exact (quarticChamberBCDFG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDFG53 hc =>
          exact (quarticChamberBCDFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG54 hc =>
          rcases quarticChamberBCDFG54810_refine A B C D E F G hc with
            h0 | h1 | h2 | h3 | h4
          · exact QuarticChamberResidual6810.rBCDFG54L0 h0
          · exact (quarticRefinedBCDFG54L1810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h1 hnc hkapDeg hxiDeg).elim
          · exact (quarticRefinedBCDFG54L2810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h2 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCDFG54L3 h3
          · exact QuarticChamberResidual6810.rBCDFG54L4 h4
        | cBCDFG55 hc =>
          exact (quarticChamberBCDFG55810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG56 hc =>
          exact (quarticChamberBCDFG56810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG57 hc =>
          exact (quarticChamberBCDFG57810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG58 hc =>
          exact (quarticChamberBCDFG58810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG59 hc =>
          exact (quarticChamberBCDFG59810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG60 hc =>
          exact (quarticChamberBCDFG60810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDFG61 hc =>
          exact (quarticChamberBCDFG61810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDFG62 hc =>
          exact (quarticChamberBCDFG62810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDFG63 hc =>
          exact (quarticChamberBCDFG63810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDFG64 hc =>
          exact (quarticChamberBCDFG64810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG65 hc =>
          exact (quarticChamberBCDFG65810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDFG66 hc =>
          exact (quarticChamberBCDFG66810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEFG0 hc =>
          exact (quarticChamberBCEFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG1 hc =>
          exact (quarticChamberBCEFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCEFG2 hc =>
          exact (quarticChamberBCEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG3 hc =>
          exact (quarticChamberBCEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG4 hc =>
          exact (quarticChamberBCEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG5 hc =>
          exact (quarticChamberBCEFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG6 hc =>
          exact (quarticChamberBCEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCEFG7 hc =>
          rcases quarticChamberBCEFG7810_refine A B C D E F G hc with
            h0 | h1 | h2
          · exact (quarticRefinedBCEFG7L0810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h0 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCEFG7L1 h1
          · exact QuarticChamberResidual6810.rBCEFG7L2 h2
        | cBCEFG8 hc =>
          exact (quarticChamberBCEFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG9 hc =>
          exact QuarticChamberResidual6810.rBCEFG9 hc
        | cBCEFG10 hc =>
          exact QuarticChamberResidual6810.rBCEFG10 hc
        | cBCEFG11 hc =>
          exact (quarticChamberBCEFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG12 hc =>
          exact (quarticChamberBCEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG13 hc =>
          exact (quarticChamberBCEFG13810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCEFG14 hc =>
          exact QuarticChamberResidual6810.rBCEFG14 hc
        | cBCEFG15 hc =>
          exact (quarticChamberBCEFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG16 hc =>
          exact (quarticChamberBCEFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG17 hc =>
          exact (quarticChamberBCEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCEFG18 hc =>
          exact (quarticChamberBCEFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG19 hc =>
          exact (quarticChamberBCEFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg).elim
        | cBCEFG20 hc =>
          exact (quarticChamberBCEFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG21 hc =>
          exact (quarticChamberBCEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG22 hc =>
          exact (quarticChamberBCEFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEFG23 hc =>
          exact (quarticChamberBCEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG24 hc =>
          exact (quarticChamberBCEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG25 hc =>
          exact (quarticChamberBCEFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG26 hc =>
          exact (quarticChamberBCEFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG27 hc =>
          exact (quarticChamberBCEFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBCEFG28 hc =>
          exact (quarticChamberBCEFG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG29 hc =>
          exact (quarticChamberBCEFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCEFG30 hc =>
          exact (quarticChamberBCEFG30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG31 hc =>
          exact (quarticChamberBCEFG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCEFG32 hc =>
          exact (quarticChamberBCEFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG33 hc =>
          exact (quarticChamberBCEFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG34 hc =>
          exact (quarticChamberBCEFG34810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG35 hc =>
          exact (quarticChamberBCEFG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG36 hc =>
          exact (quarticChamberBCEFG36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG37 hc =>
          exact (quarticChamberBCEFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCEFG38 hc =>
          exact (quarticChamberBCEFG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG39 hc =>
          exact (quarticChamberBCEFG39810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG40 hc =>
          exact (quarticChamberBCEFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG41 hc =>
          exact (quarticChamberBCEFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG42 hc =>
          exact (quarticChamberBCEFG42810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG43 hc =>
          exact (quarticChamberBCEFG43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG44 hc =>
          exact (quarticChamberBCEFG44810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG45 hc =>
          exact QuarticChamberResidual6810.rBCEFG45 hc
        | cBCEFG46 hc =>
          exact (quarticChamberBCEFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG47 hc =>
          exact (quarticChamberBCEFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG48 hc =>
          exact (quarticChamberBCEFG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCEFG49 hc =>
          exact (quarticChamberBCEFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG50 hc =>
          exact (quarticChamberBCEFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG51 hc =>
          exact (quarticChamberBCEFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG52 hc =>
          exact (quarticChamberBCEFG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCEFG53 hc =>
          exact (quarticChamberBCEFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG54 hc =>
          rcases quarticChamberBCEFG54810_refine A B C D E F G hc with
            h0 | h1 | h2
          · exact QuarticChamberResidual6810.rBCEFG54L0 h0
          · exact (quarticRefinedBCEFG54L1810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h1 hnc hkapDeg hnuDeg hxiDeg).elim
          · exact (quarticRefinedBCEFG54L2810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h2 hnc hkapDeg hnuDeg).elim
        | cBCEFG55 hc =>
          exact (quarticChamberBCEFG55810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG56 hc =>
          exact (quarticChamberBCEFG56810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG57 hc =>
          exact (quarticChamberBCEFG57810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG58 hc =>
          exact (quarticChamberBCEFG58810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG59 hc =>
          exact (quarticChamberBCEFG59810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCEFG60 hc =>
          exact (quarticChamberBCEFG60810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG61 hc =>
          exact (quarticChamberBCEFG61810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG62 hc =>
          exact (quarticChamberBCEFG62810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG63 hc =>
          exact (quarticChamberBCEFG63810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCEFG64 hc =>
          exact (quarticChamberBCEFG64810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG65 hc =>
          exact (quarticChamberBCEFG65810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCEFG66 hc =>
          exact (quarticChamberBCEFG66810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG0 hc =>
          exact (quarticChamberBDEFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG1 hc =>
          exact (quarticChamberBDEFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG2 hc =>
          exact (quarticChamberBDEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG3 hc =>
          exact (quarticChamberBDEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG4 hc =>
          exact (quarticChamberBDEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG5 hc =>
          exact (quarticChamberBDEFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG6 hc =>
          exact (quarticChamberBDEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG7 hc =>
          exact QuarticChamberResidual6810.rBDEFG7 hc
        | cBDEFG8 hc =>
          exact (quarticChamberBDEFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hxiDeg hpiDeg).elim
        | cBDEFG9 hc =>
          exact QuarticChamberResidual6810.rBDEFG9 hc
        | cBDEFG10 hc =>
          exact QuarticChamberResidual6810.rBDEFG10 hc
        | cBDEFG11 hc =>
          exact (quarticChamberBDEFG11810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG12 hc =>
          exact (quarticChamberBDEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBDEFG13 hc =>
          exact QuarticChamberResidual6810.rBDEFG13 hc
        | cBDEFG14 hc =>
          exact (quarticChamberBDEFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG15 hc =>
          exact (quarticChamberBDEFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG16 hc =>
          exact (quarticChamberBDEFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG17 hc =>
          exact (quarticChamberBDEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG18 hc =>
          exact (quarticChamberBDEFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG19 hc =>
          exact (quarticChamberBDEFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBDEFG20 hc =>
          exact (quarticChamberBDEFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG21 hc =>
          exact (quarticChamberBDEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG22 hc =>
          exact (quarticChamberBDEFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG23 hc =>
          exact (quarticChamberBDEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG24 hc =>
          exact (quarticChamberBDEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG25 hc =>
          exact (quarticChamberBDEFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG26 hc =>
          exact (quarticChamberBDEFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBDEFG27 hc =>
          exact (quarticChamberBDEFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG28 hc =>
          exact (quarticChamberBDEFG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG29 hc =>
          exact (quarticChamberBDEFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG30 hc =>
          exact (quarticChamberBDEFG30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG31 hc =>
          exact (quarticChamberBDEFG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg hpiDeg).elim
        | cBDEFG32 hc =>
          exact (quarticChamberBDEFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG33 hc =>
          exact (quarticChamberBDEFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG34 hc =>
          exact (quarticChamberBDEFG34810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG35 hc =>
          exact (quarticChamberBDEFG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG36 hc =>
          exact (quarticChamberBDEFG36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG37 hc =>
          exact (quarticChamberBDEFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG38 hc =>
          exact (quarticChamberBDEFG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG39 hc =>
          exact QuarticChamberResidual6810.rBDEFG39 hc
        | cBDEFG40 hc =>
          exact (quarticChamberBDEFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG41 hc =>
          exact (quarticChamberBDEFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG42 hc =>
          exact (quarticChamberBDEFG42810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG43 hc =>
          exact (quarticChamberBDEFG43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG44 hc =>
          exact (quarticChamberBDEFG44810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBDEFG45 hc =>
          exact (quarticChamberBDEFG45810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBDEFG46 hc =>
          exact (quarticChamberBDEFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG47 hc =>
          exact (quarticChamberBDEFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG48 hc =>
          exact (quarticChamberBDEFG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG49 hc =>
          exact (quarticChamberBDEFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG50 hc =>
          exact (quarticChamberBDEFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG51 hc =>
          exact (quarticChamberBDEFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBDEFG52 hc =>
          exact (quarticChamberBDEFG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG53 hc =>
          exact (quarticChamberBDEFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBDEFG54 hc =>
          exact (quarticChamberBDEFG54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG0 hc =>
          exact (quarticChamberCDEFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG1 hc =>
          exact QuarticChamberResidual6810.rCDEFG1 hc
        | cCDEFG2 hc =>
          exact (quarticChamberCDEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG3 hc =>
          exact QuarticChamberResidual6810.rCDEFG3 hc
        | cCDEFG4 hc =>
          exact (quarticChamberCDEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG5 hc =>
          exact QuarticChamberResidual6810.rCDEFG5 hc
        | cCDEFG6 hc =>
          exact (quarticChamberCDEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG7 hc =>
          exact QuarticChamberResidual6810.rCDEFG7 hc
        | cCDEFG8 hc =>
          exact QuarticChamberResidual6810.rCDEFG8 hc
        | cCDEFG9 hc =>
          exact QuarticChamberResidual6810.rCDEFG9 hc
        | cCDEFG10 hc =>
          exact QuarticChamberResidual6810.rCDEFG10 hc
        | cCDEFG11 hc =>
          exact QuarticChamberResidual6810.rCDEFG11 hc
        | cCDEFG12 hc =>
          exact (quarticChamberCDEFG12810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG13 hc =>
          exact QuarticChamberResidual6810.rCDEFG13 hc
        | cCDEFG14 hc =>
          exact (quarticChamberCDEFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG15 hc =>
          exact (quarticChamberCDEFG15810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG16 hc =>
          exact (quarticChamberCDEFG16810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG17 hc =>
          exact (quarticChamberCDEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG18 hc =>
          exact (quarticChamberCDEFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG19 hc =>
          exact (quarticChamberCDEFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cCDEFG20 hc =>
          exact (quarticChamberCDEFG20810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG21 hc =>
          exact (quarticChamberCDEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG22 hc =>
          exact (quarticChamberCDEFG22810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG23 hc =>
          exact (quarticChamberCDEFG23810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG24 hc =>
          exact (quarticChamberCDEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG25 hc =>
          exact QuarticChamberResidual6810.rCDEFG25 hc
        | cCDEFG26 hc =>
          exact (quarticChamberCDEFG26810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cCDEFG27 hc =>
          exact (quarticChamberCDEFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG28 hc =>
          rcases quarticChamberCDEFG28810_refine A B C D E F G hc with
            h0 | h1 | h2 | h3 | h4
          · exact QuarticChamberResidual6810.rCDEFG28L0 h0
          · exact (quarticRefinedCDEFG28L1810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h1 hnc hkapDeg hxiDeg).elim
          · exact (quarticRefinedCDEFG28L2810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h2 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rCDEFG28L3 h3
          · exact QuarticChamberResidual6810.rCDEFG28L4 h4
        | cCDEFG29 hc =>
          exact (quarticChamberCDEFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG30 hc =>
          exact (quarticChamberCDEFG30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG31 hc =>
          exact (quarticChamberCDEFG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG32 hc =>
          exact (quarticChamberCDEFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG33 hc =>
          exact (quarticChamberCDEFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG34 hc =>
          rcases quarticChamberCDEFG34810_refine A B C D E F G hc with
            h0 | h1 | h2
          · exact QuarticChamberResidual6810.rCDEFG34L0 h0
          · exact QuarticChamberResidual6810.rCDEFG34L1 h1
          · exact QuarticChamberResidual6810.rCDEFG34L2 h2
        | cCDEFG35 hc =>
          exact (quarticChamberCDEFG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG36 hc =>
          exact (quarticChamberCDEFG36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG37 hc =>
          exact (quarticChamberCDEFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG38 hc =>
          exact (quarticChamberCDEFG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cCDEFG39 hc =>
          exact QuarticChamberResidual6810.rCDEFG39 hc
        | cCDEFG40 hc =>
          exact (quarticChamberCDEFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG41 hc =>
          exact (quarticChamberCDEFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG42 hc =>
          exact (quarticChamberCDEFG42810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG43 hc =>
          exact (quarticChamberCDEFG43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cCDEFG44 hc =>
          exact (quarticChamberCDEFG44810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hxiDeg).elim
        | cCDEFG45 hc =>
          exact (quarticChamberCDEFG45810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cCDEFG46 hc =>
          exact (quarticChamberCDEFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG47 hc =>
          exact (quarticChamberCDEFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG48 hc =>
          exact (quarticChamberCDEFG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG49 hc =>
          exact (quarticChamberCDEFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG50 hc =>
          exact (quarticChamberCDEFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG51 hc =>
          exact (quarticChamberCDEFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cCDEFG52 hc =>
          exact (quarticChamberCDEFG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG53 hc =>
          exact (quarticChamberCDEFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cCDEFG54 hc =>
          exact (quarticChamberCDEFG54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
      | size6 h =>
        cases h with
        | cBCDEFG0 hc =>
          exact (quarticChamberBCDEFG0810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG1 hc =>
          exact (quarticChamberBCDEFG1810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg).elim
        | cBCDEFG2 hc =>
          exact (quarticChamberBCDEFG2810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG3 hc =>
          exact (quarticChamberBCDEFG3810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG4 hc =>
          exact (quarticChamberBCDEFG4810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG5 hc =>
          exact (quarticChamberBCDEFG5810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG6 hc =>
          exact (quarticChamberBCDEFG6810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDEFG7 hc =>
          rcases quarticChamberBCDEFG7810_refine A B C D E F G hc with
            h0 | h1 | h2 | h3 | h4 | h5 | h6
          · exact (quarticRefinedBCDEFG7L0810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h0 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCDEFG7L1 h1
          · exact QuarticChamberResidual6810.rBCDEFG7L2 h2
          · exact QuarticChamberResidual6810.rBCDEFG7L3 h3
          · exact (quarticRefinedBCDEFG7L4810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h4 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCDEFG7L5 h5
          · exact QuarticChamberResidual6810.rBCDEFG7L6 h6
        | cBCDEFG8 hc =>
          exact (quarticChamberBCDEFG8810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG9 hc =>
          exact QuarticChamberResidual6810.rBCDEFG9 hc
        | cBCDEFG10 hc =>
          exact QuarticChamberResidual6810.rBCDEFG10 hc
        | cBCDEFG11 hc =>
          exact QuarticChamberResidual6810.rBCDEFG11 hc
        | cBCDEFG12 hc =>
          exact QuarticChamberResidual6810.rBCDEFG12 hc
        | cBCDEFG13 hc =>
          exact QuarticChamberResidual6810.rBCDEFG13 hc
        | cBCDEFG14 hc =>
          exact (quarticChamberBCDEFG14810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG15 hc =>
          exact QuarticChamberResidual6810.rBCDEFG15 hc
        | cBCDEFG16 hc =>
          exact QuarticChamberResidual6810.rBCDEFG16 hc
        | cBCDEFG17 hc =>
          exact (quarticChamberBCDEFG17810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG18 hc =>
          exact (quarticChamberBCDEFG18810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG19 hc =>
          exact (quarticChamberBCDEFG19810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG20 hc =>
          exact QuarticChamberResidual6810.rBCDEFG20 hc
        | cBCDEFG21 hc =>
          exact (quarticChamberBCDEFG21810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEFG22 hc =>
          exact QuarticChamberResidual6810.rBCDEFG22 hc
        | cBCDEFG23 hc =>
          exact QuarticChamberResidual6810.rBCDEFG23 hc
        | cBCDEFG24 hc =>
          exact (quarticChamberBCDEFG24810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG25 hc =>
          exact (quarticChamberBCDEFG25810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCDEFG26 hc =>
          exact QuarticChamberResidual6810.rBCDEFG26 hc
        | cBCDEFG27 hc =>
          exact (quarticChamberBCDEFG27810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG28 hc =>
          exact (quarticChamberBCDEFG28810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG29 hc =>
          exact (quarticChamberBCDEFG29810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDEFG30 hc =>
          exact (quarticChamberBCDEFG30810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG31 hc =>
          exact (quarticChamberBCDEFG31810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEFG32 hc =>
          exact (quarticChamberBCDEFG32810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG33 hc =>
          exact (quarticChamberBCDEFG33810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG34 hc =>
          exact QuarticChamberResidual6810.rBCDEFG34 hc
        | cBCDEFG35 hc =>
          exact (quarticChamberBCDEFG35810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG36 hc =>
          exact (quarticChamberBCDEFG36810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG37 hc =>
          exact (quarticChamberBCDEFG37810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg).elim
        | cBCDEFG38 hc =>
          exact (quarticChamberBCDEFG38810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG39 hc =>
          exact (quarticChamberBCDEFG39810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG40 hc =>
          exact (quarticChamberBCDEFG40810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG41 hc =>
          exact (quarticChamberBCDEFG41810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG42 hc =>
          exact (quarticChamberBCDEFG42810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG43 hc =>
          exact (quarticChamberBCDEFG43810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG44 hc =>
          exact (quarticChamberBCDEFG44810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEFG45 hc =>
          exact (quarticChamberBCDEFG45810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG46 hc =>
          exact (quarticChamberBCDEFG46810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG47 hc =>
          exact (quarticChamberBCDEFG47810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG48 hc =>
          exact (quarticChamberBCDEFG48810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG49 hc =>
          exact (quarticChamberBCDEFG49810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG50 hc =>
          exact (quarticChamberBCDEFG50810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG51 hc =>
          exact (quarticChamberBCDEFG51810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hpiDeg).elim
        | cBCDEFG52 hc =>
          exact (quarticChamberBCDEFG52810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG53 hc =>
          exact (quarticChamberBCDEFG53810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hpiDeg).elim
        | cBCDEFG54 hc =>
          exact (quarticChamberBCDEFG54810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG55 hc =>
          exact (quarticChamberBCDEFG55810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG56 hc =>
          exact (quarticChamberBCDEFG56810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG57 hc =>
          exact (quarticChamberBCDEFG57810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG58 hc =>
          exact QuarticChamberResidual6810.rBCDEFG58 hc
        | cBCDEFG59 hc =>
          exact (quarticChamberBCDEFG59810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG60 hc =>
          exact (quarticChamberBCDEFG60810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG61 hc =>
          exact (quarticChamberBCDEFG61810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCDEFG62 hc =>
          exact (quarticChamberBCDEFG62810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG63 hc =>
          exact (quarticChamberBCDEFG63810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG64 hc =>
          exact (quarticChamberBCDEFG64810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG65 hc =>
          exact (quarticChamberBCDEFG65810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG66 hc =>
          exact (quarticChamberBCDEFG66810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG67 hc =>
          exact (quarticChamberBCDEFG67810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG68 hc =>
          exact (quarticChamberBCDEFG68810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg hpiDeg).elim
        | cBCDEFG69 hc =>
          exact (quarticChamberBCDEFG69810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG70 hc =>
          exact (quarticChamberBCDEFG70810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG71 hc =>
          exact (quarticChamberBCDEFG71810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG72 hc =>
          exact (quarticChamberBCDEFG72810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG73 hc =>
          exact (quarticChamberBCDEFG73810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG74 hc =>
          exact (quarticChamberBCDEFG74810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG75 hc =>
          exact (quarticChamberBCDEFG75810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG76 hc =>
          exact (quarticChamberBCDEFG76810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG77 hc =>
          exact (quarticChamberBCDEFG77810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG78 hc =>
          exact (quarticChamberBCDEFG78810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG79 hc =>
          exact (quarticChamberBCDEFG79810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG80 hc =>
          exact (quarticChamberBCDEFG80810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG81 hc =>
          exact QuarticChamberResidual6810.rBCDEFG81 hc
        | cBCDEFG82 hc =>
          exact (quarticChamberBCDEFG82810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEFG83 hc =>
          exact QuarticChamberResidual6810.rBCDEFG83 hc
        | cBCDEFG84 hc =>
          exact QuarticChamberResidual6810.rBCDEFG84 hc
        | cBCDEFG85 hc =>
          exact (quarticChamberBCDEFG85810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG86 hc =>
          exact (quarticChamberBCDEFG86810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG87 hc =>
          exact QuarticChamberResidual6810.rBCDEFG87 hc
        | cBCDEFG88 hc =>
          exact (quarticChamberBCDEFG88810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG89 hc =>
          exact (quarticChamberBCDEFG89810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG90 hc =>
          exact (quarticChamberBCDEFG90810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG91 hc =>
          exact (quarticChamberBCDEFG91810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG92 hc =>
          exact (quarticChamberBCDEFG92810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG93 hc =>
          exact (quarticChamberBCDEFG93810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEFG94 hc =>
          exact (quarticChamberBCDEFG94810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG95 hc =>
          exact (quarticChamberBCDEFG95810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG96 hc =>
          exact (quarticChamberBCDEFG96810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG97 hc =>
          exact (quarticChamberBCDEFG97810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG98 hc =>
          exact (quarticChamberBCDEFG98810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG99 hc =>
          exact (quarticChamberBCDEFG99810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG100 hc =>
          exact (quarticChamberBCDEFG100810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDEFG101 hc =>
          exact (quarticChamberBCDEFG101810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG102 hc =>
          rcases quarticChamberBCDEFG102810_refine A B C D E F G hc with
            h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
          · exact QuarticChamberResidual6810.rBCDEFG102L0 h0
          · exact (quarticRefinedBCDEFG102L1810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h1 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCDEFG102L2 h2
          · exact QuarticChamberResidual6810.rBCDEFG102L3 h3
          · exact QuarticChamberResidual6810.rBCDEFG102L4 h4
          · exact QuarticChamberResidual6810.rBCDEFG102L5 h5
          · exact (quarticRefinedBCDEFG102L6810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h6 hnc hkapDeg hxiDeg).elim
          · exact (quarticRefinedBCDEFG102L7810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h7 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCDEFG102L8 h8
          · exact QuarticChamberResidual6810.rBCDEFG102L9 h9
          · exact QuarticChamberResidual6810.rBCDEFG102L10 h10
          · exact (quarticRefinedBCDEFG102L11810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h11 hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
          · exact QuarticChamberResidual6810.rBCDEFG102L12 h12
          · exact (quarticRefinedBCDEFG102L13810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h13 hnc hkapDeg hxiDeg).elim
          · exact QuarticChamberResidual6810.rBCDEFG102L14 h14
        | cBCDEFG103 hc =>
          exact (quarticChamberBCDEFG103810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG104 hc =>
          exact (quarticChamberBCDEFG104810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG105 hc =>
          exact (quarticChamberBCDEFG105810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG106 hc =>
          exact (quarticChamberBCDEFG106810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG107 hc =>
          exact (quarticChamberBCDEFG107810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG108 hc =>
          rcases quarticChamberBCDEFG108810_refine A B C D E F G hc with
            h0 | h1 | h2 | h3 | h4 | h5 | h6
          · exact QuarticChamberResidual6810.rBCDEFG108L0 h0
          · exact (quarticRefinedBCDEFG108L1810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h1 hnc hkapDeg hnuDeg hxiDeg).elim
          · exact QuarticChamberResidual6810.rBCDEFG108L2 h2
          · exact (quarticRefinedBCDEFG108L3810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h3 hnc hkapDeg hnuDeg hxiDeg).elim
          · exact (quarticRefinedBCDEFG108L4810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h4 hnc hkapDeg hnuDeg).elim
          · exact QuarticChamberResidual6810.rBCDEFG108L5 h5
          · exact (quarticRefinedBCDEFG108L6810_impossible
              l beta gamma delta epsilon zeta eta theta
              A B C D E F G h6 hnc hkapDeg hnuDeg).elim
        | cBCDEFG109 hc =>
          exact (quarticChamberBCDEFG109810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG110 hc =>
          exact (quarticChamberBCDEFG110810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG111 hc =>
          exact (quarticChamberBCDEFG111810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG112 hc =>
          exact (quarticChamberBCDEFG112810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG113 hc =>
          exact (quarticChamberBCDEFG113810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG114 hc =>
          exact (quarticChamberBCDEFG114810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg hpiDeg).elim
        | cBCDEFG115 hc =>
          exact QuarticChamberResidual6810.rBCDEFG115 hc
        | cBCDEFG116 hc =>
          exact (quarticChamberBCDEFG116810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG117 hc =>
          exact (quarticChamberBCDEFG117810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG118 hc =>
          exact (quarticChamberBCDEFG118810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG119 hc =>
          exact (quarticChamberBCDEFG119810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG120 hc =>
          exact (quarticChamberBCDEFG120810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hmuDeg hxiDeg hpiDeg).elim
        | cBCDEFG121 hc =>
          exact (quarticChamberBCDEFG121810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG122 hc =>
          exact (quarticChamberBCDEFG122810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg).elim
        | cBCDEFG123 hc =>
          exact (quarticChamberBCDEFG123810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
        | cBCDEFG124 hc =>
          exact (quarticChamberBCDEFG124810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG125 hc =>
          exact (quarticChamberBCDEFG125810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG126 hc =>
          exact (quarticChamberBCDEFG126810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG127 hc =>
          exact (quarticChamberBCDEFG127810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hnuDeg hxiDeg).elim
        | cBCDEFG128 hc =>
          exact (quarticChamberBCDEFG128810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG129 hc =>
          exact (quarticChamberBCDEFG129810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG130 hc =>
          exact (quarticChamberBCDEFG130810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG131 hc =>
          exact (quarticChamberBCDEFG131810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hmuDeg).elim
        | cBCDEFG132 hc =>
          exact (quarticChamberBCDEFG132810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG133 hc =>
          exact (quarticChamberBCDEFG133810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hxiDeg).elim
        | cBCDEFG134 hc =>
          exact (quarticChamberBCDEFG134810_impossible
            l beta gamma delta epsilon zeta eta theta
            A B C D E F G hc hnc hkapDeg hpiDeg).elim
  · exact Or.inr hABCDEFG

#print axioms normalized810ScaleZero_quarticChamber6Residual

end QuarticChamberResidual6810

end Max11DegreeRoutes
