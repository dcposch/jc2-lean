import Sol610ScaleTwoDegreeZeroPostCollapseJetPart05Scratch
import Sol610ScaleTwoDegreeZeroPostCollapseJetPart04Scratch

noncomputable section
namespace Max11DegreeRoutes
open scoped Polynomial
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroPostCollapseJetEval610

variable {k : Type*} [CommRing k]

/-- At a root of the local scale the quotient evaluates to its single
degree-zero head. -/
theorem degreeZeroPostCollapseJetQuotient610_eval_root
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda a : k) (hroot : h.eval a = 0) :
    (degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseJetHead610 (p32.eval a) (q41.eval a) := by
  rw [degreeZeroPostCollapseJetQuotient610_eval, hroot,
    degreeZeroPostCollapseJetQuotient610_zero]

end DegreeZeroPostCollapseJetEval610

end Max11DegreeRoutes
