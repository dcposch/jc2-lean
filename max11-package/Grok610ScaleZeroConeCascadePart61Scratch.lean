import Grok610ScaleZeroConeCascadePart59Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
/-- If `B` is the only nonconstant free-core letter, the face `B⁵` has
degree at least five. -/
theorem uniqueNonconstantB_impossible
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hBpos : 0 < B.natDegree)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hcone : ExtremeHighBCone610 A B C0 D0 E0 := by
    refine ⟨⟨hBpos, hA.symm ▸ hBpos, hC.symm ▸ hBpos, hD.symm ▸ hBpos,
        hE.symm ▸ hBpos⟩, ?_, ?_⟩
    · omega
    · omega
  exact extremeHighB_impossible l alpha beta delta epsilon zeta eta theta
    j A B C0 D0 E0 hj hcone hder

end HighBAndDCone610

end Max11DegreeRoutes
