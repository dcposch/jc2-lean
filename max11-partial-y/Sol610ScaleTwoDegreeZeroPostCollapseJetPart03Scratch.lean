import Sol610ScaleTwoDegreeZeroCompactSourceScratch
import Sol610ScaleTwoNonzeroFourteenthPostCollapseResidualScratch

noncomputable section
namespace Max11DegreeRoutes
open scoped Polynomial
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroPostCollapseJet610

variable {R : Type*} [CommRing R]

/-- The first surviving head of the degree-zero source jet. -/
def degreeZeroPostCollapseJetHead610 (p32 q41 : R) : R :=
  (7583143431241728 : R) * p32 ^ 3 * q41

end DegreeZeroPostCollapseJet610

end Max11DegreeRoutes
