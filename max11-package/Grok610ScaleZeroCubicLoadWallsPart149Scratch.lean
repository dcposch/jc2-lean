import Grok610ScaleZeroCubicLoadWallsPart04Scratch
import Grok610ScaleZeroCubicLoadWallsPart73Scratch

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
theorem degreeZeroN2Cubic610_eq_CD_thetaWall
    (alpha epsilon eta theta : k) (A B C D E : k[X]) :
    degreeZeroN2Cubic610 0 alpha 0 0 epsilon 0 eta theta A B C D E =
      n2CubicSigmaFaceCD610 A B C D E +
        n2CubicThetaFace610 theta A +
          degreeZeroN2CubicCDWallThetaRest610 alpha epsilon eta theta
            A B C D E := by
  simp only [degreeZeroN2Cubic610, n2CubicSigmaFaceCD610, n2CubicThetaFace610,
    degreeZeroN2CubicCDWallThetaRest610,
    degreeZeroN2CubicCDWallThetaRest610_chunk0,
    degreeZeroN2CubicCDWallThetaRest610_chunk1, zero_mul, mul_zero, zero_smul]
  all_goals module

end CubicLoadWallSplits610

end Max11DegreeRoutes
