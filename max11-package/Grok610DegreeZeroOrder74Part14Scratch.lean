import Grok610DegreeZeroOrder74Part07Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610_of_fourPlus
    (h w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610 h w1 a42 p32n
        p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda =
      degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1 a42 p32n p21 p1
        p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda +
        h *
          degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610 h w1 a42
            p32n p21 p1 p0 s2 u2 b63 q1 lambda := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderThreePlus610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610,
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFourPlus610]
  ring

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
