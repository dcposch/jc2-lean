import Grok610DegreeZeroOrder73Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderFiveSplit610

variable {F : Type*} [CommRing F]

/-- On `p21 = p1 = 0` the sixty-two-term order-`72` mixin vanishes
identically (already recorded at order `73`); the order-`73` mixin
does not. -/
theorem degreeZeroPostCollapseP32Q41Q3ZeroOrderFour610_p21P1Zero_ne_head
    (w1 a42 p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 _q1 lambda : F)
    (hp21 : p21 = 0) (hp1 : p1 = 0) :
    degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610 w1 a42 p32n p21
        p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda = 0 :=
  degreeZeroPostCollapseP32Q41Q3ZeroOrderThreeHead610_p21P1Zero w1 a42
    p32n p21 p1 p0 s2 u2 b63 q53 q41n q3n q2 lambda hp21 hp1

end DegreeZeroOrderFiveSplit610

end Max11DegreeRoutes
