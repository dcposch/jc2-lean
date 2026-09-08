import Grok610DegreeZeroSplitChildrenPart04Scratch
import Grok610DegreeZeroSplitChildrenPart05Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroOrderOneHead610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetQuotient610_orderExpansion
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPostCollapseJetHead610 p32 q41 +
        h * degreeZeroPostCollapseJetOrderOne610 w1 a42 p32 p21 p1 q53
          q41 q3 u2 +
        h ^ 2 * degreeZeroPostCollapseJetOrderTwoPlus610 h w1 a42 p32
          p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
  simp only [degreeZeroPostCollapseJetQuotient610,
    degreeZeroPostCollapseJetHead610,
    degreeZeroPostCollapseJetOrderOne610,
    degreeZeroPostCollapseJetOrderTwoPlus610]
  ring

end DegreeZeroOrderOneHead610

end Max11DegreeRoutes
