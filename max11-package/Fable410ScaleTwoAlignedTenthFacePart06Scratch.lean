import Fable410ScaleTwoAlignedTenthFacePart05Scratch

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 64000000 in
/-- Squared weight-`33/2` polynomial first integral of the aligned
`(4,10)` eleventh defect: `M₁₈² = κ₁₀ H³³` — the odd-power
discriminator shape regenerated a FIFTH time, one level below the even
weight-`15` shape of the degree-`3` row. -/
theorem alignedEleventhDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
      Polynomial.C κ * H ^ 4) :
    ∃ κ₁₀ : K,
      alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
          (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 33 :=
  thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410 hH
    (alignedEleventhDefectRow_eq_zero_410 hp hq hjac hp4 hq10 haligned hM)

#print axioms alignedEleventhDefectPowerRelation_410

end Max11DegreeRoutes
