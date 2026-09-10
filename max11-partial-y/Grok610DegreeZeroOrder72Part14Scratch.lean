import Grok610DegreeZeroOrder72Part04Scratch
import Grok610DegreeZeroOrder72Part05Scratch

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
set_option maxHeartbeats 800000000

section DegreeZeroOrderThreeHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetQuotient610_p32P21P1Scale
    (h w1 a42 p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseJetQuotient610 h w1 a42 (h * p32n) (h * p21n)
        (h * p1n) p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda =
      h ^ 3 *
          degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610 w1 a42
            p32n p21n p1n p0 q41 q3 +
        h ^ 4 *
          degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610 h w1 a42
            p32n p21n p1n p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseJetQuotient610,
    degreeZeroPostCollapseJetQuotient610c0, degreeZeroPostCollapseJetQuotient610c1, degreeZeroPostCollapseJetQuotient610c2, degreeZeroPostCollapseJetQuotient610c3, degreeZeroPostCollapseJetQuotient610c4, degreeZeroPostCollapseJetQuotient610c5, degreeZeroPostCollapseJetQuotient610c6, degreeZeroPostCollapseJetQuotient610c7, degreeZeroPostCollapseJetQuotient610c8, degreeZeroPostCollapseJetQuotient610c9, degreeZeroPostCollapseJetQuotient610c10, degreeZeroPostCollapseJetQuotient610c11, degreeZeroPostCollapseJetQuotient610c12, degreeZeroPostCollapseJetQuotient610c13, degreeZeroPostCollapseJetQuotient610c14, degreeZeroPostCollapseJetQuotient610c15, degreeZeroPostCollapseJetQuotient610c16, degreeZeroPostCollapseJetQuotient610c17, degreeZeroPostCollapseJetQuotient610c18, degreeZeroPostCollapseJetQuotient610c19, degreeZeroPostCollapseJetQuotient610c20, degreeZeroPostCollapseJetQuotient610c21, degreeZeroPostCollapseJetQuotient610c22, degreeZeroPostCollapseJetQuotient610c23, degreeZeroPostCollapseJetQuotient610c24, degreeZeroPostCollapseJetQuotient610c25, degreeZeroPostCollapseJetQuotient610c26, degreeZeroPostCollapseJetQuotient610c27, degreeZeroPostCollapseJetQuotient610c28, degreeZeroPostCollapseJetQuotient610c29, degreeZeroPostCollapseJetQuotient610c30, degreeZeroPostCollapseJetQuotient610c31, degreeZeroPostCollapseJetQuotient610c32, degreeZeroPostCollapseJetQuotient610c33, degreeZeroPostCollapseJetQuotient610c34, degreeZeroPostCollapseJetQuotient610c35, degreeZeroPostCollapseJetQuotient610c36, degreeZeroPostCollapseJetQuotient610c37, degreeZeroPostCollapseJetQuotient610c38, degreeZeroPostCollapseJetQuotient610c39, degreeZeroPostCollapseJetQuotient610c40, degreeZeroPostCollapseJetQuotient610c41, degreeZeroPostCollapseJetQuotient610c42, degreeZeroPostCollapseJetQuotient610c43, degreeZeroPostCollapseJetQuotient610c44, degreeZeroPostCollapseJetQuotient610c45, degreeZeroPostCollapseJetQuotient610c46, degreeZeroPostCollapseJetQuotient610c47,
    degreeZeroPostCollapseP32P21P1ZeroOrderThreeHead610,
    degreeZeroPostCollapseP32P21P1ZeroOrderThreePlus610]
  ring

end DegreeZeroOrderThreeHead610

end Max11DegreeRoutes
