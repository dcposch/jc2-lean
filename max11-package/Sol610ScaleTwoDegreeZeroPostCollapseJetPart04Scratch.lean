import Sol610ScaleTwoDegreeZeroPostCollapseJetPart01Scratch
import Sol610ScaleTwoDegreeZeroPostCollapseJetPart03Scratch

noncomputable section
namespace Max11DegreeRoutes
open scoped Polynomial
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroPostCollapseJet610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem degreeZeroPostCollapseJetQuotient610_zero
    (w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    degreeZeroPostCollapseJetQuotient610 0 w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 lambda =
      degreeZeroPostCollapseJetHead610 p32 q41 := by
  simp only [degreeZeroPostCollapseJetQuotient610,
    degreeZeroPostCollapseJetHead610, zero_mul, zero_pow, Nat.ofNat_pos,
    add_zero, sub_zero]
  ring

end DegreeZeroPostCollapseJet610

end Max11DegreeRoutes
