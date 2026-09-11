import Sol610ScaleTwoNonzeroFourteenthPostCollapseResidualScratch
import Sol610ScaleTwoDegreeZeroPostCollapseJetPart01Scratch
import Sol610ScaleTwoDegreeZeroPostCollapseJetCompactScaledScratch

noncomputable section
namespace Max11DegreeRoutes
open scoped Polynomial
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroPostCollapseJet610

variable {R : Type*} [CommRing R]

open private memory610_compactPostCollapseScaled from Sol610ScaleTwoDegreeZeroPostCollapseJetCompactScaledScratch in
set_option maxHeartbeats 800000000 in
/-- Exact order-`69` factorization of the degree-zero compact source
numerator. -/
theorem degreeZeroClearedCompact610_postCollapse_factored
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    degreeZeroClearedCompact610
        (h ^ 10 * postCollapseNuA610 w1 a42)
        (h ^ 14 * postCollapseNuB610 h w1 a42 p32)
        (h ^ 19 * postCollapseNuC610 h w1 a42 p32 p21)
        (h ^ 24 * postCollapseNuD610 h w1 a42 p32 p21 p1)
        (h ^ 29 * postCollapseNuE610 h w1 a42 p32 p21 p1 p0)
        (h ^ 10 * postCollapseNuP610 w1 s2 lambda)
        (h ^ 14 * postCollapseNuQ610 h w1 s2 u2 lambda)
        (h ^ 19 * postCollapseNuR610 h w1 s2 u2 b63 lambda)
        (h ^ 23 * postCollapseNuS610 h w1 s2 u2 b63 q53 lambda)
        (h ^ 27 * postCollapseNuT610 h w1 s2 u2 b63 q53 q41 lambda)
        (h ^ 32 * postCollapseNuU610 h w1 s2 u2 b63 q53 q41 q3 lambda)
        (h ^ 37 * postCollapseNuV610 h w1 s2 u2 b63 q53 q41 q3 q2 lambda)
        (h ^ 42 * postCollapseNuW610 h w1 s2 u2 b63 q53 q41 q3 q2 q1
          lambda)
        (h ^ 5 * lambda) =
      h ^ 69 * degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1
        p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
  rw [memory610_compactPostCollapseScaled]
  unfold degreeZeroPostCollapseJetQuotient610 degreeZeroPostCollapseJetQuotient610c0 degreeZeroPostCollapseJetQuotient610c1 degreeZeroPostCollapseJetQuotient610c2 degreeZeroPostCollapseJetQuotient610c3 degreeZeroPostCollapseJetQuotient610c4 degreeZeroPostCollapseJetQuotient610c5 degreeZeroPostCollapseJetQuotient610c6 degreeZeroPostCollapseJetQuotient610c7 degreeZeroPostCollapseJetQuotient610c8 degreeZeroPostCollapseJetQuotient610c9 degreeZeroPostCollapseJetQuotient610c10 degreeZeroPostCollapseJetQuotient610c11 degreeZeroPostCollapseJetQuotient610c12 degreeZeroPostCollapseJetQuotient610c13 degreeZeroPostCollapseJetQuotient610c14 degreeZeroPostCollapseJetQuotient610c15 degreeZeroPostCollapseJetQuotient610c16 degreeZeroPostCollapseJetQuotient610c17 degreeZeroPostCollapseJetQuotient610c18 degreeZeroPostCollapseJetQuotient610c19 degreeZeroPostCollapseJetQuotient610c20 degreeZeroPostCollapseJetQuotient610c21 degreeZeroPostCollapseJetQuotient610c22 degreeZeroPostCollapseJetQuotient610c23 degreeZeroPostCollapseJetQuotient610c24 degreeZeroPostCollapseJetQuotient610c25 degreeZeroPostCollapseJetQuotient610c26 degreeZeroPostCollapseJetQuotient610c27 degreeZeroPostCollapseJetQuotient610c28 degreeZeroPostCollapseJetQuotient610c29 degreeZeroPostCollapseJetQuotient610c30 degreeZeroPostCollapseJetQuotient610c31 degreeZeroPostCollapseJetQuotient610c32 degreeZeroPostCollapseJetQuotient610c33 degreeZeroPostCollapseJetQuotient610c34 degreeZeroPostCollapseJetQuotient610c35 degreeZeroPostCollapseJetQuotient610c36 degreeZeroPostCollapseJetQuotient610c37 degreeZeroPostCollapseJetQuotient610c38 degreeZeroPostCollapseJetQuotient610c39 degreeZeroPostCollapseJetQuotient610c40 degreeZeroPostCollapseJetQuotient610c41 degreeZeroPostCollapseJetQuotient610c42 degreeZeroPostCollapseJetQuotient610c43 degreeZeroPostCollapseJetQuotient610c44 degreeZeroPostCollapseJetQuotient610c45 degreeZeroPostCollapseJetQuotient610c46 degreeZeroPostCollapseJetQuotient610c47 postCollapseNuA610 postCollapseNuB610 postCollapseNuC610 postCollapseNuD610 postCollapseNuE610 postCollapseNuP610 postCollapseNuQ610 postCollapseNuR610 postCollapseNuS610 postCollapseNuT610 postCollapseNuU610 postCollapseNuV610 postCollapseNuW610
  ring

end DegreeZeroPostCollapseJet610

end Max11DegreeRoutes
