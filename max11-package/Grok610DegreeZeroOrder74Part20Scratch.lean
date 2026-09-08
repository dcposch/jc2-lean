import Grok610DegreeZeroOrder74Part08Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610_p21P1Zero
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda : R)
    (hp21 : p21 = 0) (hp1 : p1 = 0) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610 w1 a42 p32n p21 p1
        p0 s2 u2 b63 q53 q41n q3n q2 q1 lambda =
      degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFour610 w1 a42 p32n
        p0 q53 q41n q3n q2 := by
  simp only [degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610,
    degreeZeroPostCollapseP32Q41Q3P21P1ZeroOrderFour610, hp21, hp1]
  ring

end DegreeZeroOrderFiveHead610

end Max11DegreeRoutes
