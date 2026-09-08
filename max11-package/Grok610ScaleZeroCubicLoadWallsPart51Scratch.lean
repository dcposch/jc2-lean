import Grok610ScaleZeroCubicLoadWallsPart42Scratch
import Grok610ScaleZeroCubicLoadWallsPart44Scratch
import Grok610ScaleZeroCubicLoadWallsPart46Scratch
import Grok610ScaleZeroCubicLoadWallsPart48Scratch
import Grok610ScaleZeroCubicLoadWallsPart50Scratch

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

section CubicLoadWallRests610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN2CubicCDWallBetaRest610_natDegree_lt
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hwall : 7 * (12 * A.natDegree) = 18 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN2CubicCDWallBetaRest610 alpha beta delta epsilon zeta eta theta A B C D E).natDegree < 6 * A.natDegree := by
  simp only [degreeZeroN2CubicCDWallBetaRest610]
  have h0 := degreeZeroN2CubicCDWallBetaRest610_chunk0_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h1 := degreeZeroN2CubicCDWallBetaRest610_chunk1_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h2 := degreeZeroN2CubicCDWallBetaRest610_chunk2_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have h3 := degreeZeroN2CubicCDWallBetaRest610_chunk3_natDegree_lt alpha beta delta epsilon zeta eta theta A B C D E hcone hwall
  have hadd01 := natDegree_add_le (degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)
  have hadd012 := natDegree_add_le ((degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) + (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)) (degreeZeroN2CubicCDWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E)
  have hadd := natDegree_add_le (((degreeZeroN2CubicCDWallBetaRest610_chunk0 alpha beta delta epsilon zeta eta theta A B C D E) + (degreeZeroN2CubicCDWallBetaRest610_chunk1 alpha beta delta epsilon zeta eta theta A B C D E)) + (degreeZeroN2CubicCDWallBetaRest610_chunk2 alpha beta delta epsilon zeta eta theta A B C D E)) (degreeZeroN2CubicCDWallBetaRest610_chunk3 alpha beta delta epsilon zeta eta theta A B C D E)
  exact lt_of_le_of_lt hadd (max_lt (lt_of_le_of_lt hadd012 (max_lt (lt_of_le_of_lt hadd01 (max_lt h0 h1)) h2)) h3)

end CubicLoadWallRests610

end Max11DegreeRoutes
