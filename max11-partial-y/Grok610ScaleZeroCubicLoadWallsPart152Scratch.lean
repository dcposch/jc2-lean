import Grok610ScaleZeroCubicLoadWallsPart89Scratch

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
set_option maxRecDepth 100000000

section CubicLoadWallSplits610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1Cubic610_eq_BCDE_deltaWall
    (alpha delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1Cubic610 0 alpha 0 delta epsilon zeta eta theta A B C D E =
      n1CubicSigmaFaceBCDE610 A B C D E +
        n1CubicDeltaFace610 delta A +
          degreeZeroN1CubicBCDEWallDeltaRest610 alpha delta epsilon zeta eta
            theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceBCDE610, n1CubicDeltaFace610,
    degreeZeroN1CubicBCDEWallDeltaRest610,
    degreeZeroN1CubicBCDEWallDeltaRest610_chunk0,
    degreeZeroN1CubicBCDEWallDeltaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

end CubicLoadWallSplits610

end Max11DegreeRoutes
